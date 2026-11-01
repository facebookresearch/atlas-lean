/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Logic.Embedding.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.Finset.Powerset

/-!
# Hoeffding's U-statistics: unbiasedness and the variance formula

For a kernel `h : αᵐ → ℝ` and a sample `x : αⁿ` with `m ≤ n`, the U-statistic is the average of
`h` over all `n (n - 1) ⋯ (n - m + 1)` injective choices of `m` sample indices:
`U(x) = (n)_m⁻¹ ∑_{f : Fin m ↪ Fin n} h(x ∘ f)`. For a symmetric kernel this equals Hoeffding's
average `C(n, m)⁻¹ ∑_{i₁ < ⋯ < i_m} h(x_{i₁}, …, x_{i_m})` over `m`-subsets.

For an i.i.d. sample from `μ`:

* `U` is an unbiased estimator of `θ = E h(X₁, …, X_m)`;
* (**Hoeffding 1948**) for a symmetric square-integrable kernel,
  `Var U = C(n, m)⁻¹ ∑_{c=1}^{m} C(m, c) C(n - m, m - c) σ_c²`, where `σ_c² = Var h_c` and
  `h_c(y₁, …, y_c) = E h(y₁, …, y_c, X_{c+1}, …, X_m)` is the `c`-th projection of `h`.

The asymptotic normality `√n (U - θ) ⇒ N(0, m² σ₁²)` is not covered here.

## Main results

* `uStatistic`, `hoeffdingProj`.
* `integral_uStatistic`: unbiasedness.
* `variance_uStatistic`: Hoeffding's variance formula.

## References

* W. Hoeffding, *A class of statistics with asymptotically normal distribution*, Ann. Math.
  Statist. 19 (1948), 293–325 (§§4–5).
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {α : Type*} [MeasurableSpace α]

/-- The U-statistic with kernel `h` of degree `m` on a sample `x` of size `n`: the average of
`h (x ∘ f)` over the `n.descFactorial m` injective maps `f : Fin m ↪ Fin n`. For `m > n` there
are no such maps and the value is `0` (Lean's `a / 0 = 0`). -/
noncomputable def uStatistic {m n : ℕ} (h : (Fin m → α) → ℝ) (x : Fin n → α) : ℝ :=
  (∑ f : Fin m ↪ Fin n, h (x ∘ f)) / n.descFactorial m

/-- Hoeffding's `c`-th projection of a kernel `h` of degree `m` under `μ`:
`h_c(y) = E h(y₁, …, y_c, X_{c+1}, …, X_m)` with `X_{c+1}, …, X_m` i.i.d. `μ`. -/
noncomputable def hoeffdingProj (μ : Measure α) {m : ℕ} (h : (Fin m → α) → ℝ) (c : ℕ)
    (y : Fin c → α) : ℝ :=
  ∫ z : Fin (m - c) → α,
    h (fun j => if hj : (j : ℕ) < c then y ⟨j, hj⟩ else z ⟨j - c, by have := j.isLt; omega⟩)
    ∂(Measure.pi fun _ => μ)

private theorem measurePreserving_coordinates {α I J : Type*} [MeasurableSpace α]
    [Fintype I] [Fintype J] (μ : Measure α) [IsProbabilityMeasure μ] (f : I ↪ J) :
    MeasurePreserving (fun x : J → α => x ∘ f)
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  classical
  refine ⟨Measurable.of_eval (fun j => measurable_pi_apply (f j)), ?_⟩
  have hind : iIndepFun (fun i (x : J → α) => x i) (Measure.pi fun _ => μ) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hmap := (hind.precomp f.injective).map_fun_eq_pi_map
    (fun j => (measurable_pi_apply (f j)).aemeasurable)
  simpa only [Function.comp_def, (measurePreserving_eval (fun _ : J => μ) _).map_eq]
    using hmap

/-- **Unbiasedness**: for an i.i.d. sample of size `n ≥ m` and an integrable kernel, the
U-statistic has mean `E h(X₁, …, X_m)`. -/
theorem integral_uStatistic {m n : ℕ} (hmn : m ≤ n) (μ : Measure α) [IsProbabilityMeasure μ]
    {h : (Fin m → α) → ℝ} (hh : Integrable h (Measure.pi fun _ => μ)) :
    ∫ x, uStatistic h x ∂(Measure.pi fun _ : Fin n => μ) =
      ∫ y, h y ∂(Measure.pi fun _ => μ) := by
  classical
  have hp (f : Fin m ↪ Fin n) := measurePreserving_coordinates μ f
  have hi (f : Fin m ↪ Fin n) :
      Integrable (fun x : Fin n → α => h (x ∘ f)) (Measure.pi fun _ => μ) :=
    (hp f).integrable_comp_of_integrable hh
  have he (f : Fin m ↪ Fin n) :
      (∫ x : Fin n → α, h (x ∘ f) ∂(Measure.pi fun _ => μ)) =
        ∫ y, h y ∂(Measure.pi fun _ => μ) := by
    rw [← integral_map (hp f).aemeasurable ((hp f).map_eq.symm ▸ hh.aestronglyMeasurable)]
    rw [(hp f).map_eq]
  have hn : (n.descFactorial m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hmn).ne'
  simp only [uStatistic, integral_div]
  rw [integral_finsetSum _ (fun f _ => hi f)]
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq,
    Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hn

private theorem variance_uStatistic_covariances {α : Type*} [MeasurableSpace α]
    {m n : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    {h : (Fin m → α) → ℝ} (hh : MemLp h 2 (Measure.pi fun _ => μ)) :
    Var[uStatistic h; Measure.pi fun _ : Fin n => μ] =
      (∑ f : Fin m ↪ Fin n, ∑ g : Fin m ↪ Fin n,
        cov[fun x => h (x ∘ f), fun x => h (x ∘ g); Measure.pi fun _ => μ]) /
        (n.descFactorial m : ℝ) ^ 2 := by
  classical
  have hi (f : Fin m ↪ Fin n) :
      MemLp (fun x : Fin n → α => h (x ∘ f)) 2 (Measure.pi fun _ => μ) :=
    hh.comp_measurePreserving (measurePreserving_coordinates μ f)
  change Var[fun x : Fin n → α =>
    (∑ f : Fin m ↪ Fin n, h (x ∘ f)) / n.descFactorial m; _] = _
  simp only [div_eq_mul_inv]
  rw [variance_mul_const, variance_fun_sum hi]
  simp only [inv_pow]

private theorem memLp_integral_right {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {H : A × B → ℝ}
    (hH : MemLp H 2 (μ.prod ν)) :
    MemLp (fun y => ∫ z, H (y, z) ∂ν) 2 μ := by
  have hP := hH.aestronglyMeasurable.integral_prod_right'
  apply (memLp_two_iff_integrable_sq hP).mpr
  have hHi := hH.integrable (by norm_num)
  have hHs := hH.integrable_sq
  have hsec : ∀ᵐ y ∂μ, MemLp (fun z => H (y, z)) 2 ν := by
    filter_upwards [hHi.prod_right_ae, hHs.prod_right_ae] with y hy hys
    exact (memLp_two_iff_integrable_sq hy.aestronglyMeasurable).mpr hys
  refine hHs.integral_prod_left.mono' (hP.pow 2) ?_
  filter_upwards [hsec] with y hy
  have hb := variance_nonneg (fun z => H (y, z)) ν
  rw [variance_eq_sub hy] at hb
  dsimp only [Pi.pow_apply] at hb
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  linarith

private theorem covariance_shared_product {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {H : A × B → ℝ}
    (hH : MemLp H 2 (μ.prod ν)) :
    cov[fun p : A × (B × B) => H (p.1, p.2.1),
      fun p : A × (B × B) => H (p.1, p.2.2); μ.prod (ν.prod ν)] =
      Var[fun y => ∫ z, H (y, z) ∂ν; μ] := by
  have hf : MeasurePreserving (fun p : A × (B × B) => (p.1, p.2.1))
      (μ.prod (ν.prod ν)) (μ.prod ν) :=
    (MeasurePreserving.id μ).prod measurePreserving_fst
  have hg : MeasurePreserving (fun p : A × (B × B) => (p.1, p.2.2))
      (μ.prod (ν.prod ν)) (μ.prod ν) :=
    (MeasurePreserving.id μ).prod measurePreserving_snd
  have hi : MemLp (fun p : A × (B × B) => H (p.1, p.2.1)) 2
      (μ.prod (ν.prod ν)) := hH.comp_measurePreserving hf
  have hj : MemLp (fun p : A × (B × B) => H (p.1, p.2.2)) 2
      (μ.prod (ν.prod ν)) := hH.comp_measurePreserving hg
  have he (f : A × (B × B) → A × B)
      (hp : MeasurePreserving f (μ.prod (ν.prod ν)) (μ.prod ν)) :
      (∫ p, H (f p) ∂(μ.prod (ν.prod ν))) = ∫ q, H q ∂(μ.prod ν) := by
    rw [← integral_map hp.aemeasurable (hp.map_eq.symm ▸ hH.aestronglyMeasurable)]
    rw [hp.map_eq]
  rw [covariance_eq_sub hi hj, variance_eq_sub (memLp_integral_right μ ν hH)]
  rw [he _ hf, he _ hg, integral_prod H (hH.integrable (by norm_num))]
  rw [integral_prod _ (hi.integrable_mul hj)]
  simp only [Pi.mul_apply, pow_two]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  exact integral_prod_mul (fun z => H (y, z)) (fun z => H (y, z))

private theorem measurePreserving_prefix_join {α : Type*} [MeasurableSpace α]
    {m c : ℕ} (hc : c ≤ m) (μ : Measure α) [IsProbabilityMeasure μ] :
    MeasurePreserving
      (fun p : (Fin c → α) × (Fin (m - c) → α) =>
        fun j : Fin m => if hj : (j : ℕ) < c then p.1 ⟨j, hj⟩
          else p.2 ⟨j - c, by have := j.isLt; omega⟩)
      ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))
      (Measure.pi fun _ => μ) := by
  let e : Fin c ⊕ Fin (m - c) ≃ Fin m :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hc))
  have hp := (measurePreserving_piCongrLeft (fun _ : Fin m => μ) e).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin c ⊕ Fin (m - c) => μ))
  convert hp using 1
  funext p j
  obtain ⟨i, rfl⟩ := e.surjective j
  cases i with
  | inl i =>
    rw [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
    simp [e, Equiv.trans_apply, finSumFinEquiv, i.isLt]
    rfl
  | inr i =>
    rw [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
    simp [e, Equiv.trans_apply, finSumFinEquiv, Nat.not_lt.mpr (Nat.le_add_right c i)]
    rfl

private theorem reorder_selection {α I : Type*} [MeasurableSpace α]
    [DecidableEq I] {m c : ℕ} (hc : c ≤ m) (f : Fin m ↪ I)
    (S T : Finset I) (hST : Disjoint S T) (hR : S ∪ T = Finset.univ.map f)
    (eS : Fin c ≃ S) (eT : Fin (m - c) ≃ T)
    (h : (Fin m → α) → ℝ)
    (hsymm : ∀ (σ : Equiv.Perm (Fin m)) y, h (y ∘ σ) = h y) (x : I → α) :
    h (x ∘ f) = h (fun j => if hj : (j : ℕ) < c then x (eS ⟨j, hj⟩)
      else x (eT ⟨j - c, by have := j.isLt; omega⟩)) := by
  classical
  let R := Finset.univ.map f
  let ef : Fin m ≃ R := Equiv.ofBijective
    (fun i => ⟨f i, Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun i j hij => f.injective (congrArg Subtype.val hij), by
      intro y
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp y.property
      exact ⟨i, Subtype.ext hi⟩⟩
  let eu : S ⊕ T ≃ R := (Equiv.Finset.union S T hST).trans
    (Set.equivOfEq (congrArg (fun s : Finset I => (s : Set I)) hR))
  let en : Fin c ⊕ Fin (m - c) ≃ Fin m :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hc))
  let σ : Equiv.Perm (Fin m) := en.symm.trans ((Equiv.sumCongr eS eT).trans
    (eu.trans ef.symm))
  rw [← hsymm σ (x ∘ f)]
  congr 1
  funext j
  obtain ⟨i, rfl⟩ := en.surjective j
  have hef (k : Fin m) : (ef k : I) = f k := rfl
  change x (f (σ (en i))) = _
  rw [← hef, show ef (σ (en i)) = eu ((Equiv.sumCongr eS eT) i) by simp [σ]]
  cases i with
  | inl i =>
    simp [en, eu, Equiv.trans_apply, finSumFinEquiv, i.isLt]
    rfl
  | inr i =>
    simp [en, eu, Equiv.trans_apply, finSumFinEquiv, Nat.not_lt.mpr (Nat.le_add_right c i)]
    rfl

private theorem measurePreserving_three_blocks {α : Type*} [MeasurableSpace α]
    {n c k : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (S A B : Finset (Fin n)) (hSA : Disjoint S A) (hSB : Disjoint S B)
    (hAB : Disjoint A B) (eS : Fin c ≃ S) (eA : Fin k ≃ A) (eB : Fin k ≃ B) :
    MeasurePreserving (fun x : Fin n → α =>
      (fun i => x (eS i), (fun i => x (eA i), fun i => x (eB i))))
      (Measure.pi fun _ => μ)
      ((Measure.pi fun _ => μ).prod
        ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))) := by
  let E : Fin c ⊕ (Fin k ⊕ Fin k) ↪ Fin n :=
    ⟨Sum.elim (fun i => (eS i : Fin n))
      (Sum.elim (fun i => (eA i : Fin n)) (fun i => (eB i : Fin n))), by
      rintro (i | (i | i)) (j | (j | j)) hij <;> dsimp only [Sum.elim_inl, Sum.elim_inr] at hij
      · exact congrArg Sum.inl (eS.injective (Subtype.ext hij))
      · exact False.elim (Finset.disjoint_left.mp hSA (eS i).property
          (hij.symm ▸ (eA j).property))
      · exact False.elim (Finset.disjoint_left.mp hSB (eS i).property
          (hij.symm ▸ (eB j).property))
      · exact False.elim (Finset.disjoint_left.mp hSA (hij ▸ (eS j).property)
          (eA i).property)
      · exact congrArg (Sum.inr ∘ Sum.inl) (eA.injective (Subtype.ext hij))
      · exact False.elim (Finset.disjoint_left.mp hAB (eA i).property
          (hij.symm ▸ (eB j).property))
      · exact False.elim (Finset.disjoint_left.mp hSB (hij ▸ (eS j).property)
          (eB i).property)
      · exact False.elim (Finset.disjoint_left.mp hAB (hij ▸ (eA j).property)
          (eB i).property)
      · exact congrArg (Sum.inr ∘ Sum.inr) (eB.injective (Subtype.ext hij))⟩
  have hp := ((MeasurePreserving.id (Measure.pi fun _ : Fin c => μ)).prod
    (measurePreserving_sumPiEquivProdPi (fun _ : Fin k ⊕ Fin k => μ))).comp
      ((measurePreserving_sumPiEquivProdPi (fun _ : Fin c ⊕ (Fin k ⊕ Fin k) => μ)).comp
        (measurePreserving_coordinates μ E))
  convert hp using 1
  rfl

private theorem covariance_overlap {α : Type*} [MeasurableSpace α]
    {m n : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    {h : (Fin m → α) → ℝ}
    (hsymm : ∀ (σ : Equiv.Perm (Fin m)) y, h (y ∘ σ) = h y)
    (hh : MemLp h 2 (Measure.pi fun _ => μ)) (f g : Fin m ↪ Fin n) :
    cov[fun x => h (x ∘ f), fun x => h (x ∘ g); Measure.pi fun _ => μ] =
      Var[hoeffdingProj μ h ((Finset.univ.map f) ∩ (Finset.univ.map g)).card;
        Measure.pi fun _ => μ] := by
  classical
  let F := Finset.univ.map f
  let G := Finset.univ.map g
  let S := F ∩ G
  let A := F \ G
  let B := G \ F
  let c := S.card
  have hFcard : F.card = m := by simp [F]
  have hGcard : G.card = m := by simp [G]
  have hc : c ≤ m := by
    simpa only [c, hFcard] using Finset.card_le_card (Finset.inter_subset_left : S ⊆ F)
  have hAc : A.card = m - c := by
    simp only [A, Finset.card_sdiff, Finset.inter_comm G F, hFcard, c, S]
  have hBc : B.card = m - c := by
    simp only [B, Finset.card_sdiff, hGcard, c, S]
  let eS := (Finset.equivFinOfCardEq (show S.card = c from rfl)).symm
  let eA := (Finset.equivFinOfCardEq hAc).symm
  let eB := (Finset.equivFinOfCardEq hBc).symm
  have hSA : Disjoint S A := by
    apply Finset.disjoint_left.mpr
    intro i hs ha
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp hs).2
  have hSB : Disjoint S B := by
    apply Finset.disjoint_left.mpr
    intro i hs hb
    exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_inter.mp hs).1
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  have hSF : S ∪ A = F := by
    ext i
    simp only [S, A, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hSG : S ∪ B = G := by
    ext i
    simp only [S, B, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  let H : (Fin c → α) × (Fin (m - c) → α) → ℝ := fun p =>
    h (fun j => if hj : (j : ℕ) < c then p.1 ⟨j, hj⟩
      else p.2 ⟨j - c, by have := j.isLt; omega⟩)
  have hH : MemLp H 2 ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) :=
    hh.comp_measurePreserving (measurePreserving_prefix_join hc μ)
  let Z : (Fin n → α) → (Fin c → α) × ((Fin (m - c) → α) × (Fin (m - c) → α)) :=
    fun x => (fun i => x (eS i), (fun i => x (eA i), fun i => x (eB i)))
  have hp : MeasurePreserving Z (Measure.pi fun _ => μ)
      ((Measure.pi fun _ => μ).prod
        ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))) :=
    measurePreserving_three_blocks μ S A B hSA hSB hAB eS eA eB
  have hpf : MeasurePreserving
      (fun p : (Fin c → α) × ((Fin (m - c) → α) × (Fin (m - c) → α)) =>
        (p.1, p.2.1))
      ((Measure.pi fun _ => μ).prod
        ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)))
      ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) :=
    (MeasurePreserving.id _).prod measurePreserving_fst
  have hpg : MeasurePreserving
      (fun p : (Fin c → α) × ((Fin (m - c) → α) × (Fin (m - c) → α)) =>
        (p.1, p.2.2))
      ((Measure.pi fun _ => μ).prod
        ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)))
      ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) :=
    (MeasurePreserving.id _).prod measurePreserving_snd
  have hi : MemLp (fun p => H (p.1, p.2.1)) 2
      ((Measure.pi fun _ => μ).prod
        ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))) :=
    hH.comp_measurePreserving hpf
  have hj : MemLp (fun p => H (p.1, p.2.2)) 2
      ((Measure.pi fun _ => μ).prod
        ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))) :=
    hH.comp_measurePreserving hpg
  have hf : (fun x => h (x ∘ f)) = fun x => H ((Z x).1, (Z x).2.1) := by
    funext x
    exact reorder_selection hc f S A hSA hSF eS eA h hsymm x
  have hg : (fun x => h (x ∘ g)) = fun x => H ((Z x).1, (Z x).2.2) := by
    funext x
    exact reorder_selection hc g S B hSB hSG eS eB h hsymm x
  have he := covariance_map_fun (hp.map_eq.symm ▸ hi.aestronglyMeasurable)
    (hp.map_eq.symm ▸ hj.aestronglyMeasurable) hp.aemeasurable
  rw [hp.map_eq] at he
  rw [hf, hg, ← he]
  exact covariance_shared_product _ _ hH

open Finset in
private theorem count_overlap {I : Type*} [DecidableEq I]
    (U S : Finset I) (hSU : S ⊆ U) {m c : ℕ} (hSm : S.card = m) (hc : c ≤ m) :
    ((U.powersetCard m).filter (fun T => (S ∩ T).card = c)).card =
      m.choose c * (U.card - m).choose (m - c) := by
  let P := (S.powersetCard c) ×ˢ ((U \ S).powersetCard (m - c))
  have he : ((U.powersetCard m).filter (fun T => (S ∩ T).card = c)) =
      P.image (fun p => p.1 ∪ p.2) := by
    ext T
    simp only [mem_filter, mem_powersetCard, mem_image, mem_product, P]
    constructor
    · rintro ⟨⟨hTU, hTm⟩, hST⟩
      refine ⟨(S ∩ T, T \ S), ⟨⟨inter_subset_left, hST⟩, ?_⟩, ?_⟩
      · refine ⟨?_, by rw [card_sdiff, hST, hTm]⟩
        intro i hi
        exact mem_sdiff.mpr ⟨hTU (mem_sdiff.mp hi).1, (mem_sdiff.mp hi).2⟩
      · ext i
        simp only [mem_union, mem_inter, mem_sdiff]
        tauto
    · rintro ⟨⟨A, B⟩, ⟨⟨hAS, hAc⟩, ⟨hBU, hBm⟩⟩, rfl⟩
      have hd : Disjoint A B := disjoint_of_subset_left hAS
        (disjoint_of_subset_right hBU disjoint_sdiff_self_right)
      have hi : S ∩ (A ∪ B) = A := by
        ext i
        have hb : i ∈ B → i ∉ S := fun hi => (mem_sdiff.mp (hBU hi)).2
        have ha : i ∈ A → i ∈ S := fun hi => hAS hi
        simp only [mem_inter, mem_union]
        tauto
      refine ⟨⟨union_subset (hAS.trans hSU) (hBU.trans sdiff_subset), ?_⟩, ?_⟩
      · rw [card_union_of_disjoint hd, hAc, hBm]
        omega
      · rw [hi, hAc]
  have hinj : Set.InjOn (fun p : Finset I × Finset I => p.1 ∪ p.2) P := by
    rintro ⟨A, B⟩ hp ⟨A', B'⟩ hp' heq
    have hAS := (mem_powersetCard.mp (mem_product.mp hp).1).1
    have hBS := (mem_powersetCard.mp (mem_product.mp hp).2).1
    have hAS' := (mem_powersetCard.mp (mem_product.mp hp').1).1
    have hBS' := (mem_powersetCard.mp (mem_product.mp hp').2).1
    apply Prod.ext
    · ext i
      have hb : i ∈ B → i ∉ S := fun hi => (mem_sdiff.mp (hBS hi)).2
      have hb' : i ∈ B' → i ∉ S := fun hi => (mem_sdiff.mp (hBS' hi)).2
      have hm := congrArg (fun T => i ∈ T) heq
      simp only [mem_union] at hm
      have ha : i ∈ A → i ∈ S := fun hi => hAS hi
      have ha' : i ∈ A' → i ∈ S := fun hi => hAS' hi
      tauto
    · ext i
      have hb : i ∈ B → i ∉ S := fun hi => (mem_sdiff.mp (hBS hi)).2
      have hb' : i ∈ B' → i ∉ S := fun hi => (mem_sdiff.mp (hBS' hi)).2
      have hm := congrArg (fun T => i ∈ T) heq
      simp only [mem_union] at hm
      have ha : i ∈ A → i ∈ S := fun hi => hAS hi
      have ha' : i ∈ A' → i ∈ S := fun hi => hAS' hi
      tauto
  rw [he, card_image_of_injOn hinj]
  simp only [P, card_product, card_powersetCard, card_sdiff_of_subset hSU, hSm]

private theorem count_embedding_range {m n : ℕ} (T : Finset (Fin n)) (hTm : T.card = m) :
    ((Finset.univ : Finset (Fin m ↪ Fin n)).filter
      (fun g => Finset.univ.map g = T)).card = m.factorial := by
  classical
  let E : ↥((Finset.univ : Finset (Fin m ↪ Fin n)).filter
      (fun g => Finset.univ.map g = T)) ≃ (Fin m ↪ T) :=
    { toFun := fun g => g.val.codRestrict T (fun i => by
        change g.val i ∈ T
        have hi : g.val i ∈ Finset.univ.map g.val :=
          Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
        simpa only [(Finset.mem_filter.mp g.property).2] using hi)
      invFun := fun g => ⟨g.trans (Function.Embedding.subtype (· ∈ T)), by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        apply Finset.eq_of_subset_of_card_le
        · intro i hi
          obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
          exact (g j).property
        · simp [hTm]⟩
      left_inv := fun g => by
        apply Subtype.ext
        ext i
        rfl
      right_inv := fun g => by
        ext i
        rfl }
  have he := Fintype.card_congr E
  simpa only [Fintype.card_coe, Fintype.card_embedding_eq, Fintype.card_fin, hTm,
    Nat.descFactorial_self] using he

private theorem sum_embedding_ranges {m n : ℕ} (W : Finset (Fin n) → ℝ) :
    (∑ g : Fin m ↪ Fin n, W (Finset.univ.map g)) =
      (m.factorial : ℝ) * ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard m, W T := by
  classical
  have hm (g : Fin m ↪ Fin n) :
      Finset.univ.map g ∈ (Finset.univ : Finset (Fin n)).powersetCard m := by
    simp [Finset.mem_powersetCard]
  rw [← Finset.sum_fiberwise_of_maps_to (fun g _ => hm g)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  have he := count_embedding_range T (Finset.mem_powersetCard.mp hT).2
  rw [← he]
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro g hg
  rw [(Finset.mem_filter.mp hg).2]

private theorem sum_subset_overlaps {m n : ℕ} (S : Finset (Fin n)) (hSm : S.card = m)
    (W : ℕ → ℝ) :
    (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard m, W (S ∩ T).card) =
      ∑ c ∈ Finset.range (m + 1),
        (m.choose c : ℝ) * ((n - m).choose (m - c) : ℝ) * W c := by
  classical
  have hb (T : Finset (Fin n)) : (S ∩ T).card < m + 1 := by
    have he := Finset.card_le_card (Finset.inter_subset_left : S ∩ T ⊆ S)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to (fun T _ => Finset.mem_range.mpr (hb T))]
  apply Finset.sum_congr rfl
  intro c hc
  have hm : c ≤ m := by have := Finset.mem_range.mp hc; omega
  have he := count_overlap Finset.univ S (Finset.subset_univ _) hSm hm
  rw [show (∑ T ∈ ((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun T => (S ∩ T).card = c), W (S ∩ T).card) =
      ∑ _T ∈ ((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun T => (S ∩ T).card = c), W c from
    Finset.sum_congr rfl (fun T hT => congrArg W (Finset.mem_filter.mp hT).2)]
  simp only [Finset.sum_const, he, nsmul_eq_mul, Nat.cast_mul, Finset.card_univ,
    Fintype.card_fin]

private theorem sum_embedding_overlaps {m n : ℕ} (S : Finset (Fin n)) (hSm : S.card = m)
    (W : ℕ → ℝ) :
    (∑ g : Fin m ↪ Fin n, W (S ∩ (Finset.univ.map g)).card) =
      (m.factorial : ℝ) * ∑ c ∈ Finset.range (m + 1),
        (m.choose c : ℝ) * ((n - m).choose (m - c) : ℝ) * W c := by
  rw [sum_embedding_ranges (fun T => W (S ∩ T).card), sum_subset_overlaps S hSm W]

private theorem variance_projection_zero {α : Type*} [MeasurableSpace α]
    {m : ℕ} (μ : Measure α) [IsProbabilityMeasure μ] (h : (Fin m → α) → ℝ) :
    Var[hoeffdingProj μ h 0; Measure.pi fun _ : Fin 0 => μ] = 0 := by
  have he : hoeffdingProj μ h 0 = fun _ => hoeffdingProj μ h 0 Fin.elim0 := by
    funext y
    congr 1
    exact Subsingleton.elim _ _
  rw [he, variance_eq_integral measurable_const.aemeasurable]
  simp

/-- **Hoeffding's variance formula** (1948, §5): for an i.i.d. sample of size `n ≥ m`
and a symmetric square-integrable kernel `h` of degree `m`,
`Var U = C(n, m)⁻¹ ∑_{c=1}^{m} C(m, c) C(n - m, m - c) Var h_c`. -/
theorem variance_uStatistic {m n : ℕ} (hmn : m ≤ n) (μ : Measure α) [IsProbabilityMeasure μ]
    {h : (Fin m → α) → ℝ} (hsymm : ∀ (σ : Equiv.Perm (Fin m)) y, h (y ∘ σ) = h y)
    (hh : MemLp h 2 (Measure.pi fun _ => μ)) :
    Var[uStatistic h; Measure.pi fun _ : Fin n => μ] =
      (∑ c ∈ Finset.Icc 1 m, (m.choose c : ℝ) * ((n - m).choose (m - c) : ℝ) *
        Var[hoeffdingProj μ h c; Measure.pi fun _ : Fin c => μ]) / n.choose m := by
  classical
  let W (c : ℕ) := Var[hoeffdingProj μ h c; Measure.pi fun _ : Fin c => μ]
  have hW : W 0 = 0 := variance_projection_zero μ h
  have hs : (∑ c ∈ Finset.range (m + 1),
      (m.choose c : ℝ) * ((n - m).choose (m - c) : ℝ) * W c) =
      ∑ c ∈ Finset.Icc 1 m,
        (m.choose c : ℝ) * ((n - m).choose (m - c) : ℝ) * W c := by
    symm
    apply Finset.sum_subset
    · intro c hc
      have := Finset.mem_Icc.mp hc
      exact Finset.mem_range.mpr (by omega)
    · intro c hc hn
      have hc0 : c = 0 := by
        have := Finset.mem_range.mp hc
        have hnot : ¬(1 ≤ c ∧ c ≤ m) := by simpa only [Finset.mem_Icc] using hn
        omega
      simp [hc0, hW]
  rw [variance_uStatistic_covariances μ hh]
  simp_rw [covariance_overlap μ hsymm hh]
  have hin (f : Fin m ↪ Fin n) :
      (∑ g : Fin m ↪ Fin n, W ((Finset.univ.map f) ∩ (Finset.univ.map g)).card) =
        (m.factorial : ℝ) * ∑ c ∈ Finset.range (m + 1),
          (m.choose c : ℝ) * ((n - m).choose (m - c) : ℝ) * W c :=
    sum_embedding_overlaps (Finset.univ.map f) (by simp) W
  change (∑ f : Fin m ↪ Fin n, ∑ g : Fin m ↪ Fin n,
    W ((Finset.univ.map f) ∩ (Finset.univ.map g)).card) /
      (n.descFactorial m : ℝ) ^ 2 = _
  simp_rw [hin]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq,
    Fintype.card_fin, nsmul_eq_mul]
  rw [hs]
  have he : (n.descFactorial m : ℝ) = (m.factorial : ℝ) * (n.choose m : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose n m
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hn : (n.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmn).ne'
  rw [he]
  field_simp
  rfl

end ProbabilityTheory
