/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorPower.UnshuffleCoordinates
public import MathlibExt.LinearAlgebra.ExteriorAlgebra.CoalgebraDiagonal
import Lean.Elab.Tactic.Omega

/-!
# Unshuffle components of the exterior coproduct

For `E=ExteriorAlgebra R M`, the coproduct of a word `w : Fin N → M` expands over all subsets
`s ⊆ Fin N`. The term for `s` sends its selected vectors to the first exterior factor and its
complement to the second, retaining word order and the graded tensor signs.

When `N=p+q`, a subset of cardinality `p` gives the matching signed two-block tensor under
bidegree projection; the other subsets project to zero. Thus `(π_p ⊗ π_q) ∘ Δ` restricted to
`Λ^(p+q)_R M` is the full unshuffle map. Both empty blocks are included.

References: Bourbaki, *Algebra*, Chapter III; Loday, *Cyclic Homology*, Section 4.5.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v

namespace exteriorPower

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

open AlgebraicTopology.EilenbergZilber

local notation "E" => ExteriorAlgebra R M
local notation "ℰ" => fun n : ℕ => ⋀[R]^n M
local notation "G" => ℰ ᵍ⊗[R] ℰ
local notation "π" => projection R M

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E=ExteriorAlgebra R M`. Let `G` be the
graded tensor algebra of the two exterior degree families, `τ : E⊗E ≃ₗ[R] G`, and `P :
ExteriorAlgebra R (M×M) ≃ₐ[R] G` the product equivalence. For `N : ℕ`, `s : Finset(Fin N)`,
and `w : Fin N → M`, put `v_s(i)=(w i,0)` on `s` and `(0,w i)` elsewhere. The mixed term is
`τ⁻¹(P(ιMulti_R v_s))`. -/
def coproductMixedTerm (N : ℕ) (s : Finset (Fin N)) (w : Fin N → M) : E ⊗[R] E :=
  (GradedTensorProduct.of R ℰ ℰ).symm (ExteriorAlgebra.prodEquivTensor R M M
    (ExteriorAlgebra.ιMulti R N
      (s.piecewise (fun i => (w i, 0)) (fun i => (0, w i)))))

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E=ExteriorAlgebra R M`. Write `Δ` for
the exterior coproduct and `π_r : E → Λ^r_R M` for degree projection. For `N : ℕ` and `w : Fin
N → M`, `Δ(ExteriorAlgebra.ιMulti R N w) = ∑ s : Finset(Fin N), coproductMixedTerm R M N s w`. -/
theorem coproduct_ιMulti_mixedTerms (N : ℕ) (w : Fin N → M) :
    ExteriorAlgebra.coproduct R M (ExteriorAlgebra.ιMulti R N w) =
      ∑ s : Finset (Fin N), coproductMixedTerm R M N s w := by
  let F : (M × M) [⋀^Fin N]→ₗ[R] G :=
    (ExteriorAlgebra.prodEquivTensor R M M).toLinearMap.compAlternatingMap
      (ExteriorAlgebra.ιMulti R N)
  have hfunctions : ((fun i : Fin N => (w i, 0)) + (fun i : Fin N => (0, w i))) =
      (fun i : Fin N => (w i, w i)) := by
    funext i
    apply Prod.ext <;> simp
  have hF : F (fun i => (w i, w i)) =
      ∑ s : Finset (Fin N), F (s.piecewise (fun i => (w i, 0)) (fun i => (0, w i))) := by
    simpa only [hfunctions] using
      F.map_add_univ (fun i => (w i, 0)) (fun i => (0, w i))
  have h := congrArg (GradedTensorProduct.of R ℰ ℰ).symm hF
  rw [ExteriorAlgebra.coproduct_eq_diagonalLinear]
  change (GradedTensorProduct.of R ℰ ℰ).symm (ExteriorAlgebra.prodEquivTensor R M M
      (ExteriorAlgebra.map ((LinearMap.id : M →ₗ[R] M).prod LinearMap.id)
        (ExteriorAlgebra.ιMulti R N w))) = _
  rw [ExteriorAlgebra.map_apply_ιMulti]
  simp only [F, LinearMap.compAlternatingMap_apply, AlgEquiv.toLinearMap_apply,
    map_sum, coproductMixedTerm] at h
  exact h

private theorem mixedWord_sorted (p q : ℕ) (s : Shuffle p q) (w : Fin (p + q) → M) :
    (s.leftPositions.val.piecewise (fun i => (w i, 0)) (fun i => (0, w i))) ∘ s.perm =
      Fin.append (fun i : Fin p => (w (s.perm (Fin.castAdd q i)), 0))
        (fun j : Fin q => (0, w (s.perm (Fin.natAdd p j)))) := by
  funext k
  obtain ⟨x, rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).surjective k
  cases x with
  | inl i =>
      have hi : s.perm (Fin.castAdd q i) ∈ s.leftPositions.val := by
        change s.perm (Fin.castAdd q i) ∈ s.leftPositions
        rw [Shuffle.mem_leftPositions_iff]
        exact ⟨i, rfl⟩
      simp only [finSumFinEquiv_apply_left, Function.comp_apply, Fin.append_left,
        Finset.piecewise_eq_of_mem _ _ _ hi]
  | inr j =>
      have hj : s.perm (Fin.natAdd p j) ∉ s.leftPositions.val := by
        apply (Shuffle.mem_rightPositions_iff_not_mem_leftPositions s _).mp
        rw [Shuffle.mem_rightPositions_iff]
        exact ⟨j, rfl⟩
      simp only [finSumFinEquiv_apply_right, Function.comp_apply, Fin.append_right,
        Finset.piecewise_eq_of_notMem _ _ _ hj]

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E=ExteriorAlgebra R M`. Write `Δ` for
the exterior coproduct and `π_r : E → Λ^r_R M` for degree projection. Let `p,q : ℕ`, `s :
Shuffle p q`, and `w : Fin(p+q) → M`. The mixed term at `s.leftPositions` equals `sign(s.perm)
• (ExteriorAlgebra.ιMulti_R(fun i ↦ w(s.perm(Fin.castAdd q i))) ⊗ ExteriorAlgebra.ιMulti_R(fun
j ↦ w(s.perm(Fin.natAdd p j)))))`. -/
theorem coproductMixedTerm_shuffle (p q : ℕ) (s : Shuffle p q) (w : Fin (p + q) → M) :
    coproductMixedTerm R M (p + q) s.leftPositions.val w = Equiv.Perm.sign s.perm •
      (ExteriorAlgebra.ιMulti R p (fun i => w (s.perm (Fin.castAdd q i))) ⊗ₜ[R]
        ExteriorAlgebra.ιMulti R q (fun j => w (s.perm (Fin.natAdd p j)))) := by
  let v : Fin (p + q) → M × M :=
    s.leftPositions.val.piecewise (fun i => (w i, 0)) (fun i => (0, w i))
  have hp : ExteriorAlgebra.ιMulti R (p + q) v = Equiv.Perm.sign s.perm •
      ExteriorAlgebra.ιMulti R (p + q)
        (Fin.append (fun i : Fin p => (w (s.perm (Fin.castAdd q i)), 0))
          (fun j : Fin q => (0, w (s.perm (Fin.natAdd p j))))) := by
    rw [(ExteriorAlgebra.ιMulti R (p + q)).map_congr_perm v s.perm]
    rw [mixedWord_sorted M p q s w]
  have hf : ExteriorAlgebra.prodEquivTensor R M M
      (ExteriorAlgebra.ιMulti R (p + q)
        (Fin.append (fun i : Fin p => (w (s.perm (Fin.castAdd q i)), 0))
          (fun j : Fin q => (0, w (s.perm (Fin.natAdd p j)))))) =
      (ExteriorAlgebra.ιMulti R p (fun i => w (s.perm (Fin.castAdd q i)))) ᵍ⊗ₜ[R]
        ExteriorAlgebra.ιMulti R q (fun j => w (s.perm (Fin.natAdd p j))) := by
    have h := ExteriorAlgebra.prodEquivTensor_symm_apply_tmul_ιMulti R M M p q
      (fun i => w (s.perm (Fin.castAdd q i))) (fun j => w (s.perm (Fin.natAdd p j)))
    exact (congrArg (ExteriorAlgebra.prodEquivTensor R M M) h).symm.trans
      ((ExteriorAlgebra.prodEquivTensor R M M).apply_symm_apply _)
  unfold coproductMixedTerm
  change (GradedTensorProduct.of R ℰ ℰ).symm
    (ExteriorAlgebra.prodEquivTensor R M M (ExteriorAlgebra.ιMulti R (p + q) v)) = _
  rw [hp]
  simp only [Units.smul_def, map_zsmul]
  rw [hf]
  rfl

/-- Let `R` be a commutative ring, `M` an `R`-module, `p,q : ℕ`, `s : Shuffle p q`, and `w :
Fin(p+q) → M`. For degree projections `π_r : ExteriorAlgebra R M → Λ^r_R M`, `(π_p ⊗
π_q)(coproductMixedTerm R M (p+q) s.leftPositions w)` is `sign(s.perm) • (ιMulti_R(fun i ↦
w(s.perm(Fin.castAdd q i))) ⊗ ιMulti_R(fun j ↦ w(s.perm(Fin.natAdd p j)))))`. -/
theorem projectedMixedTerm_shuffle (p q : ℕ) (s : Shuffle p q) (w : Fin (p + q) → M) :
    TensorProduct.map (π p) (π q) (coproductMixedTerm R M (p + q) s.leftPositions.val w) =
      Equiv.Perm.sign s.perm •
        (ιMulti R p (fun i => w (s.perm (Fin.castAdd q i))) ⊗ₜ[R]
          ιMulti R q (fun j => w (s.perm (Fin.natAdd p j)))) := by
  rw [coproductMixedTerm_shuffle]
  simp only [Units.smul_def, map_zsmul, TensorProduct.map_tmul, projection_ιMulti_self]

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E=ExteriorAlgebra R M`. Write `Δ` for
the exterior coproduct and `π_r : E → Λ^r_R M` for degree projection. For `N,p,q : ℕ`, `s :
Finset(Fin N)` with `s.card≠p`, and `w : Fin N → M`, `(π_p ⊗ π_q)(coproductMixedTerm R M N s
w)=0`. -/
theorem projectedMixedTerm_ne (N p q : ℕ) (s : Finset (Fin N)) (hs : s.card ≠ p)
    (w : Fin N → M) : TensorProduct.map (π p) (π q) (coproductMixedTerm R M N s w) = 0 := by
  have hcard : s.card + sᶜ.card = N := by
    have hsN : s.card ≤ N := by simpa only [Fintype.card_fin] using Finset.card_le_univ s
    rw [Finset.card_compl, Fintype.card_fin]
    exact Nat.add_sub_of_le hsN
  generalize hk : s.card = k at *
  generalize hl : sᶜ.card = l at *
  subst N
  let a : Set.powersetCard (Fin (k + l)) k := ⟨s, hk⟩
  have ha : (Shuffle.ofLeftPositions a).leftPositions.val = s :=
    congrArg Subtype.val (Shuffle.leftPositions_ofLeftPositions a)
  rw [← ha, coproductMixedTerm_shuffle]
  simp only [Units.smul_def, map_zsmul, TensorProduct.map_tmul,
    projection_ιMulti_ne R M p k hs, TensorProduct.zero_tmul, smul_zero]

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E=ExteriorAlgebra R M`. Write `Δ` for
the exterior coproduct and `π_r : E → Λ^r_R M` for degree projection. Let `p,q : ℕ`,
`L(i)=Fin.castAdd q i`, and `R_b(j)=Fin.natAdd p j`. For `w : Fin(p+q) → M`, `(π_p ⊗
π_q)(Δ(ExteriorAlgebra.ιMulti R (p+q) w)) = ∑ s : Shuffle p q, sign(s.perm) • (ιMulti_R(w ∘
s.perm ∘ L) ⊗ ιMulti_R(w ∘ s.perm ∘ R_b))`. -/
theorem projectedCoproduct_ιMulti_shuffles (p q : ℕ) (w : Fin (p + q) → M) :
    TensorProduct.map (π p) (π q)
        (ExteriorAlgebra.coproduct R M (ExteriorAlgebra.ιMulti R (p + q) w)) =
      ∑ s : Shuffle p q, Equiv.Perm.sign s.perm •
        (ιMulti R p (fun i => w (s.perm (Fin.castAdd q i))) ⊗ₜ[R]
          ιMulti R q (fun j => w (s.perm (Fin.natAdd p j)))) := by
  classical
  rw [coproduct_ιMulti_mixedTerms, map_sum]
  let F : Finset (Fin (p + q)) → ((⋀[R]^p M) ⊗[R] (⋀[R]^q M)) := fun a =>
    TensorProduct.map (π p) (π q) (coproductMixedTerm R M (p + q) a w)
  have hz : (∑ a : {a : Finset (Fin (p + q)) // a.card ≠ p}, F a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact projectedMixedTerm_ne R M (p + q) p q a.val a.property w
  have hsplit := (Equiv.sumCompl (fun a : Finset (Fin (p + q)) => a.card = p)).sum_comp F
  rw [Fintype.sum_sum_type] at hsplit
  simp only [Equiv.sumCompl] at hsplit
  replace hsplit : (∑ a : Set.powersetCard (Fin (p + q)) p, F a.val) +
      (∑ a : {a : Finset (Fin (p + q)) // a.card ≠ p}, F a.val) =
      ∑ a : Finset (Fin (p + q)), F a := by
    have hi : (inferInstance : Fintype (Set.powersetCard (Fin (p + q)) p)) =
        (Subtype.fintype (fun a : Finset (Fin (p + q)) => a.card = p)) :=
      Subsingleton.elim _ _
    change Set.powersetCard.instFintypeElemFinset (Fin (p + q)) p =
      Subtype.fintype (fun a : Finset (Fin (p + q)) => a.card = p) at hi
    rw [hi]
    exact hsplit
  rw [hz, add_zero] at hsplit
  change (∑ a : Finset (Fin (p + q)), F a) = _
  rw [← hsplit]
  calc
    (∑ a : Set.powersetCard (Fin (p + q)) p, F a.val) =
      ∑ s : Shuffle p q, F s.leftPositions.val :=
        (Shuffle.equivLeftPositions.sum_comp (fun a => F a.val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      exact projectedMixedTerm_shuffle R M p q s w

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E=ExteriorAlgebra R M`. Write `Δ` for
the exterior coproduct and `π_r : E → Λ^r_R M` for degree projection. For `p,q : ℕ`, `(π_p ⊗
π_q) ∘ Δ ∘ j_(p+q) = unshuffle R M p q`, where `j_(p+q) : Λ^(p+q)_R M → E` is the homogeneous
inclusion. -/
theorem projectedCoproduct_eq_unshuffle (p q : ℕ) :
    (TensorProduct.map (π p) (π q)).comp
        ((ExteriorAlgebra.coproduct R M).comp (⋀[R]^(p + q) M).subtype) = unshuffle R M p q := by
  apply exteriorPower.linearMap_ext (R := R) (n := p + q) (M := M)
    (N := ((⋀[R]^p M) ⊗[R] (⋀[R]^q M)))
  apply AlternatingMap.ext
  intro w
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, ιMulti_apply_coe]
  rw [projectedCoproduct_ιMulti_shuffles, unshuffle_apply_ιMulti_shuffles]

end exteriorPower
