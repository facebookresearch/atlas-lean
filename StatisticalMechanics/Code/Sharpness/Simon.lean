/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Ising.GKS
import Code.Ising.GKS2

open scoped BigOperators symmDiff
open Finset

set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]














noncomputable def wJ (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (s : ConfigSpace V) : ℝ :=
  Real.exp ((∑ e ∈ E, J e * bond s e) + ∑ x, hf x * spin s x)


lemma wJ_pos (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ) (s : ConfigSpace V) :
    0 < wJ E J hf s := Real.exp_pos _

lemma wJ_nonneg (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ) (s : ConfigSpace V) :
    0 ≤ wJ E J hf s := (wJ_pos E J hf s).le


noncomputable def ZJ (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ) : ℝ :=
  ∑ s : ConfigSpace V, wJ E J hf s


lemma ZJ_pos (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ) : 0 < ZJ E J hf := by
  unfold ZJ
  exact Finset.sum_pos (fun s _ => wJ_pos E J hf s) Finset.univ_nonempty


noncomputable def expJ (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (f : ConfigSpace V → ℝ) : ℝ :=
  (∑ s : ConfigSpace V, f s * wJ E J hf s) / ZJ E J hf






lemma inner_sum_nonneg' (E : Finset (Sym2 V))
    (ce de : Sym2 V → ℝ) (cx dx : V → ℝ)
    (hce : ∀ e ∈ E, 0 ≤ ce e) (hde : ∀ e ∈ E, 0 ≤ de e)
    (hcx : ∀ x, 0 ≤ cx x) (hdx : ∀ x, 0 ≤ dx x)
    (obs : ConfigSpace V → ℝ) (hobs : IsSpinMonomial obs) :
    0 ≤ ∑ s : ConfigSpace V,
        obs s * ((∏ e ∈ E, (ce e + bond s e * de e))
          * (∏ x : V, (cx x + spin s x * dx x))) := by
  classical
  set C : Sym2 V ⊕ V → ℝ := Sum.elim ce cx with hC
  set D : Sym2 V ⊕ V → ℝ := Sum.elim de dx with hD
  set fac : (Sym2 V ⊕ V) → ConfigSpace V → ℝ :=
    Sum.elim (fun e s => bond s e) (fun x s => spin s x) with hfac
  set I : Finset (Sym2 V ⊕ V) :=
    E.map ⟨Sum.inl, Sum.inl_injective⟩
      ∪ Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩ with hI
  
  have hmem_inl : ∀ {e : Sym2 V}, (Sum.inl e : Sym2 V ⊕ V) ∈ I → e ∈ E := by
    intro e he
    rw [hI, Finset.mem_union] at he
    rcases he with h | h
    · simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at h
      obtain ⟨a, ha, hae⟩ := h
      rw [Sum.inl.injEq] at hae; subst hae; exact ha
    · simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at h
      obtain ⟨a, _, ha⟩ := h
      exact (Sum.inl_ne_inr ha.symm).elim
  have hint : ∀ s : ConfigSpace V,
      obs s * ((∏ e ∈ E, (ce e + bond s e * de e))
          * (∏ x : V, (cx x + spin s x * dx x)))
        = obs s * ∏ i ∈ I, (C i + D i * fac i s) := by
    intro s
    congr 1
    have hdisj : Disjoint (E.map ⟨Sum.inl, Sum.inl_injective⟩)
        ((Finset.univ : Finset V).map ⟨Sum.inr, Sum.inr_injective⟩) := by
      rw [Finset.disjoint_left]
      intro i hi hj
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hi hj
      obtain ⟨a, _, rfl⟩ := hi
      obtain ⟨b, _, hb⟩ := hj
      exact Sum.inl_ne_inr hb.symm
    rw [hI, Finset.prod_union hdisj, Finset.prod_map, Finset.prod_map]
    simp only [hC, hD, hfac, Function.Embedding.coeFn_mk, Sum.elim_inl, Sum.elim_inr]
    congr 1
    · exact Finset.prod_congr rfl (fun e _ => by ring)
    · exact Finset.prod_congr rfl (fun x _ => by ring)
  simp_rw [hint]
  apply gks_kernel I C D
  · intro i hi; rcases i with e | x
    · exact hce e (hmem_inl hi)
    · exact hcx x
  · intro i hi; rcases i with e | x
    · exact hde e (hmem_inl hi)
    · exact hdx x
  · intro i _; rcases i with e | x
    · exact isSpinMonomial_bond e
    · exact isSpinMonomial_spin x
  · exact hobs







omit [DecidableEq V] in
lemma doubled_wJ_factor (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (σ q : ConfigSpace V) :
    wJ E J hf σ * wJ E J hf (xnor σ q)
      = (∏ e ∈ E,
          (Real.cosh (J e * (1 + bond q e)) + bond σ e * Real.sinh (J e * (1 + bond q e))))
        * (∏ x : V,
          (Real.cosh (hf x * (1 + spin q x)) + spin σ x * Real.sinh (hf x * (1 + spin q x)))) := by
  rw [wJ, wJ, ← Real.exp_add]
  have hexp :
      ((∑ e ∈ E, J e * bond σ e) + ∑ x, hf x * spin σ x)
      + ((∑ e ∈ E, J e * bond (xnor σ q) e) + ∑ x, hf x * spin (xnor σ q) x)
      = (∑ e ∈ E, (J e * (1 + bond q e)) * bond σ e)
        + (∑ x, (hf x * (1 + spin q x)) * spin σ x) := by
    simp_rw [bond_xnor, spin_xnor]
    have eEdge : (∑ e ∈ E, (J e * (1 + bond q e)) * bond σ e)
        = (∑ e ∈ E, J e * bond σ e) + (∑ e ∈ E, J e * (bond σ e * bond q e)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun e _ => by ring)
    have eVert : (∑ x, (hf x * (1 + spin q x)) * spin σ x)
        = (∑ x, hf x * spin σ x) + (∑ x, hf x * (spin σ x * spin q x)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [eEdge, eVert]; ring
  rw [hexp, Real.exp_add, Real.exp_sum, Real.exp_sum]
  congr 1
  · exact Finset.prod_congr rfl (fun e _ =>
      exp_mul_pm (J e * (1 + bond q e)) (bond σ e) (bond_eq_pm σ e))
  · exact Finset.prod_congr rfl (fun x _ =>
      exp_mul_pm (hf x * (1 + spin q x)) (spin σ x) (spin_eq_pm σ x))








lemma inner_q_nonneg_J (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (hhf : ∀ x, 0 ≤ hf x) (A B : Finset V) (q : ConfigSpace V) :
    0 ≤ ∑ σ : ConfigSpace V,
      (spinProd (A ∆ B) σ * wJ E J hf σ * wJ E J hf (xnor σ q)
        - spinProd A σ * wJ E J hf σ
            * (spinProd B (xnor σ q) * wJ E J hf (xnor σ q))) := by
  have key : ∀ σ : ConfigSpace V,
      (spinProd (A ∆ B) σ * wJ E J hf σ * wJ E J hf (xnor σ q)
        - spinProd A σ * wJ E J hf σ
            * (spinProd B (xnor σ q) * wJ E J hf (xnor σ q)))
      = (1 - spinProd B q) *
          ((spinProd A σ * spinProd B σ) *
            ((∏ e ∈ E,
                (Real.cosh (J e * (1 + bond q e)) + bond σ e * Real.sinh (J e * (1 + bond q e))))
              * (∏ x : V,
                (Real.cosh (hf x * (1 + spin q x))
                  + spin σ x * Real.sinh (hf x * (1 + spin q x)))))) := by
    intro σ
    rw [← doubled_wJ_factor E J hf σ q, spinProd_xnor, ← spinProd_mul_self]
    ring
  rw [Finset.sum_congr rfl (fun σ _ => key σ), ← Finset.mul_sum]
  apply mul_nonneg (one_sub_spinProd_nonneg B q)
  
  
  exact inner_sum_nonneg' E
    (fun e => Real.cosh (J e * (1 + bond q e)))
    (fun e => Real.sinh (J e * (1 + bond q e)))
    (fun x => Real.cosh (hf x * (1 + spin q x)))
    (fun x => Real.sinh (hf x * (1 + spin q x)))
    (fun e _ => (Real.cosh_pos _).le)
    (fun e he => Real.sinh_nonneg_iff.mpr (mul_nonneg (hJ e he) (one_add_bond_nonneg q e)))
    (fun x => (Real.cosh_pos _).le)
    (fun x => Real.sinh_nonneg_iff.mpr (mul_nonneg (hhf x) (one_add_spin_nonneg q x)))
    (fun s => spinProd A s * spinProd B s)
    ((isSpinMonomial_spinProd A).mul (isSpinMonomial_spinProd B))











lemma unnorm_gks2_J (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (hhf : ∀ x, 0 ≤ hf x) (A B : Finset V) :
    (∑ s, spinProd A s * wJ E J hf s) * (∑ s, spinProd B s * wJ E J hf s)
      ≤ (∑ s, spinProd (A ∆ B) s * wJ E J hf s) * (∑ s, wJ E J hf s) := by
  rw [← sub_nonneg]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  rw [← Finset.sum_sub_distrib]
  rw [sum_dbl_reindex (fun p =>
      spinProd (A ∆ B) p.1 * wJ E J hf p.1 * wJ E J hf p.2
        - spinProd A p.1 * wJ E J hf p.1 * (spinProd B p.2 * wJ E J hf p.2))]
  rw [Fintype.sum_prod_type_right]
  exact Finset.sum_nonneg (fun q _ => inner_q_nonneg_J E J hf hJ hhf A B q)










theorem gks_second_J (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (hhf : ∀ x, 0 ≤ hf x) (A B : Finset V) :
    expJ E J hf (spinProd A) * expJ E J hf (spinProd B)
      ≤ expJ E J hf (spinProd (A ∆ B)) := by
  unfold expJ
  have hZ : 0 < ZJ E J hf := ZJ_pos E J hf
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hZ]
  have hsum : (∑ s, wJ E J hf s) = ZJ E J hf := rfl
  calc (∑ s, spinProd A s * wJ E J hf s) * (∑ s, spinProd B s * wJ E J hf s)
          * ZJ E J hf
      ≤ ((∑ s, spinProd (A ∆ B) s * wJ E J hf s) * (∑ s, wJ E J hf s)) * ZJ E J hf :=
        mul_le_mul_of_nonneg_right (unnorm_gks2_J E J hf hJ hhf A B) hZ.le
    _ = (∑ s, spinProd (A ∆ B) s * wJ E J hf s) * (ZJ E J hf * ZJ E J hf) := by
        rw [hsum]; ring







lemma wJ_insert (e₀ : Sym2 V) (E : Finset (Sym2 V)) (he : e₀ ∉ E)
    (J : Sym2 V → ℝ) (hf : V → ℝ) (s : ConfigSpace V) :
    wJ (insert e₀ E) J hf s = Real.exp (J e₀ * bond s e₀) * wJ E J hf s := by
  unfold wJ
  rw [Finset.sum_insert he, ← Real.exp_add]
  ring_nf

omit [Fintype V] in


lemma bond_eq_spinProd_pair (s : ConfigSpace V) {x y : V} (hxy : x ≠ y) :
    bond s s(x, y) = spinProd {x, y} s := by
  rw [bond_mk, spinProd, Finset.prod_pair hxy]










lemma griffiths_mono_insert (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (hhf : ∀ x, 0 ≤ hf x)
    {x y : V} (hxy : x ≠ y) (he : s(x, y) ∉ E) (hJe : 0 ≤ J s(x, y))
    (A : Finset V) :
    expJ E J hf (spinProd A) ≤ expJ (insert s(x, y) E) J hf (spinProd A) := by
  set c : ℝ := Real.cosh (J s(x, y)) with hc
  set sh : ℝ := Real.sinh (J s(x, y)) with hsh
  
  set Z₀ : ℝ := ∑ s, wJ E J hf s with hZ₀
  set Z₁ : ℝ := ∑ s, spinProd {x, y} s * wJ E J hf s with hZ₁
  set N₀ : ℝ := ∑ s, spinProd A s * wJ E J hf s with hN₀
  set N₁ : ℝ := ∑ s, spinProd (A ∆ {x, y}) s * wJ E J hf s with hN₁
  have hZ₀pos : 0 < Z₀ := ZJ_pos E J hf
  
  have hZb : (∑ s, wJ (insert s(x, y) E) J hf s) = c * Z₀ + sh * Z₁ := by
    rw [hZ₀, hZ₁, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [wJ_insert s(x, y) E he J hf s]
    rw [exp_mul_pm (J s(x, y)) (bond s s(x, y)) (bond_eq_pm s s(x, y))]
    rw [bond_eq_spinProd_pair s hxy]
    ring
  have hNb : (∑ s, spinProd A s * wJ (insert s(x, y) E) J hf s) = c * N₀ + sh * N₁ := by
    rw [hN₀, hN₁, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [wJ_insert s(x, y) E he J hf s]
    rw [exp_mul_pm (J s(x, y)) (bond s s(x, y)) (bond_eq_pm s s(x, y))]
    rw [bond_eq_spinProd_pair s hxy]
    rw [← spinProd_mul_self A {x, y}]
    ring
  have hZbpos : 0 < ZJ (insert s(x, y) E) J hf := ZJ_pos (insert s(x, y) E) J hf
  
  have hgks : N₀ * Z₁ ≤ N₁ * Z₀ := by
    have := unnorm_gks2_J E J hf hJ hhf A {x, y}
    
    simpa [hN₀, hN₁, hZ₀, hZ₁] using this
  
  rw [expJ, expJ]
  have hZbeq : ZJ (insert s(x, y) E) J hf = c * Z₀ + sh * Z₁ := by
    rw [ZJ]; exact hZb
  have hZ₀eq : ZJ E J hf = Z₀ := rfl
  rw [hZ₀eq, hNb, hZbeq]
  rw [div_le_div_iff₀ hZ₀pos (by rw [← hZbeq]; exact hZbpos)]
  
  have hshnn : 0 ≤ sh := Real.sinh_nonneg_iff.mpr hJe
  nlinarith [mul_nonneg hshnn (sub_nonneg.mpr hgks)]

omit [Fintype V] in

lemma exists_pair_of_not_isDiag {e₀ : Sym2 V} (h : ¬ e₀.IsDiag) :
    ∃ x y : V, x ≠ y ∧ e₀ = s(x, y) := by
  induction e₀ with
  | h x y =>
    refine ⟨x, y, ?_, rfl⟩
    intro hxy; exact h (Sym2.mk_isDiag_iff.mpr hxy)



lemma griffiths_mono_insert_edge (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (hhf : ∀ x, 0 ≤ hf x)
    {e₀ : Sym2 V} (hdiag : ¬ e₀.IsDiag) (he : e₀ ∉ E) (hJe : 0 ≤ J e₀)
    (A : Finset V) :
    expJ E J hf (spinProd A) ≤ expJ (insert e₀ E) J hf (spinProd A) := by
  obtain ⟨x, y, hxy, rfl⟩ := exists_pair_of_not_isDiag hdiag
  exact griffiths_mono_insert E J hf hJ hhf hxy he hJe A









lemma griffiths_mono_union (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hhf : ∀ x, 0 ≤ hf x) (A : Finset V) :
    ∀ D : Finset (Sym2 V), Disjoint D E → (∀ e ∈ D, ¬ e.IsDiag) →
      (∀ e ∈ D ∪ E, 0 ≤ J e) →
      expJ E J hf (spinProd A) ≤ expJ (D ∪ E) J hf (spinProd A) := by
  intro D
  induction D using Finset.induction with
  | empty =>
    intro _ _ _
    rw [Finset.empty_union]
  | @insert e₀ D he₀ IH =>
    intro hdisj hdiag hJ
    
    have hJDE : ∀ e ∈ D ∪ E, 0 ≤ J e := by
      intro e he
      apply hJ
      rw [Finset.mem_union] at he ⊢
      rcases he with h | h
      · exact Or.inl (Finset.mem_insert_of_mem h)
      · exact Or.inr h
    
    have hdisjD : Disjoint D E :=
      hdisj.mono_left (Finset.subset_insert e₀ D)
    
    have hdiagD : ∀ e ∈ D, ¬ e.IsDiag :=
      fun e he => hdiag e (Finset.mem_insert_of_mem he)
    
    have hdiag0 : ¬ e₀.IsDiag := hdiag e₀ (Finset.mem_insert_self e₀ D)
    have hJ0 : 0 ≤ J e₀ := hJ e₀ (Finset.mem_union.mpr (Or.inl (Finset.mem_insert_self e₀ D)))
    have he₀DE : e₀ ∉ D ∪ E := by
      rw [Finset.mem_union, not_or]
      refine ⟨he₀, ?_⟩
      intro hmem
      exact (Finset.disjoint_left.mp hdisj (Finset.mem_insert_self e₀ D)) hmem
    
    calc expJ E J hf (spinProd A)
        ≤ expJ (D ∪ E) J hf (spinProd A) := IH hdisjD hdiagD hJDE
      _ ≤ expJ (insert e₀ (D ∪ E)) J hf (spinProd A) :=
          griffiths_mono_insert_edge (D ∪ E) J hf hJDE hhf hdiag0 he₀DE hJ0 A
      _ = expJ (insert e₀ D ∪ E) J hf (spinProd A) := by
          rw [Finset.insert_union]













theorem griffiths_mono (E₁ E₂ : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hsub : E₁ ⊆ E₂) (hJ : ∀ e ∈ E₂, 0 ≤ J e) (hhf : ∀ x, 0 ≤ hf x)
    (hdiag : ∀ e ∈ E₂, e ∉ E₁ → ¬ e.IsDiag) (A : Finset V) :
    expJ E₁ J hf (spinProd A) ≤ expJ E₂ J hf (spinProd A) := by
  classical
  
  have hunion : (E₂ \ E₁) ∪ E₁ = E₂ := Finset.sdiff_union_of_subset hsub
  have hdisj : Disjoint (E₂ \ E₁) E₁ := Finset.sdiff_disjoint
  have hdiagD : ∀ e ∈ E₂ \ E₁, ¬ e.IsDiag := by
    intro e he
    rw [Finset.mem_sdiff] at he
    exact hdiag e he.1 he.2
  have hJDE : ∀ e ∈ (E₂ \ E₁) ∪ E₁, 0 ≤ J e := by
    intro e he
    rw [hunion] at he
    exact hJ e he
  have := griffiths_mono_union E₁ J hf hhf A (E₂ \ E₁) hdisj hdiagD hJDE
  rwa [hunion] at this




theorem griffiths_mono_spin (E₁ E₂ : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hsub : E₁ ⊆ E₂) (hJ : ∀ e ∈ E₂, 0 ≤ J e) (hhf : ∀ x, 0 ≤ hf x)
    (hdiag : ∀ e ∈ E₂, e ∉ E₁ → ¬ e.IsDiag) (z : V) :
    expJ E₁ J hf (spinProd {z}) ≤ expJ E₂ J hf (spinProd {z}) :=
  griffiths_mono E₁ E₂ J hf hsub hJ hhf hdiag {z}




theorem griffiths_mono_pair (E₁ E₂ : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hsub : E₁ ⊆ E₂) (hJ : ∀ e ∈ E₂, 0 ≤ J e) (hhf : ∀ x, 0 ≤ hf x)
    (hdiag : ∀ e ∈ E₂, e ∉ E₁ → ¬ e.IsDiag) (x y : V) :
    expJ E₁ J hf (spinProd {x, y}) ≤ expJ E₂ J hf (spinProd {x, y}) :=
  griffiths_mono E₁ E₂ J hf hsub hJ hhf hdiag {x, y}

end Sharpness

end StatMech
