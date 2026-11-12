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
  `h_c(y₁, …, y_c) = E h(y₁, …, y_c, X_{c+1}, …, X_m)` is the `c`-th projection of `h`;
* (**Hájek projection**) with `Ĥ = θ + (m / n) ∑ᵢ (h₁(Xᵢ) - θ)`,
  `E[(U - Ĥ)²] = Var U - m² σ₁² / n`, `n Var U → m² σ₁²` and `n E[(U - Ĥ)²] → 0`.

The asymptotic normality `√n (U - θ) ⇒ N(0, m² σ₁²)` is not covered here.

## Main results

* `uStatistic`, `hoeffdingProj`.
* `integral_uStatistic`: unbiasedness.
* `variance_uStatistic`: Hoeffding's variance formula.
* `hajekProjection`: the first-order (Hájek) projection of the U-statistic, built from the
  symmetrized kernel `h̃` and centred at `E h̃`, so that it is correct for any kernel (intended
  regime `m ≤ n`); `hajekProjection_eq_of_symm` gives the familiar form for a symmetric kernel.
* `integral_uStatistic_sub_mul_hoeffdingProj_one_sub`: `Cov(U, h₁(Xᵢ)) = (m / n) σ₁²`.
* `integral_sq_uStatistic_sub_hajekProjection`: the L² identity for the projection remainder.
* `tendsto_mul_variance_uStatistic`: `n Var U → m² σ₁²`.
* `tendsto_mul_integral_sq_uStatistic_sub_hajekProjection`: `n E[(U - Ĥ)²] → 0`.

## References

* W. Hoeffding, *A class of statistics with asymptotically normal distribution*, Ann. Math.
  Statist. 19 (1948), 293–325 (§§4–5).
* J. Hájek, *Asymptotic normality of simple linear rank statistics under alternatives*,
  Ann. Math. Statist. 39 (1968), 325–346.
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

/-! ### The Hájek projection -/

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped Topology

/-- The Hájek projection of the U-statistic with kernel `h` of degree `m` on a sample of size
`n`: `θ̃ + (m / n) ∑_{i} (h̃₁(x_i) - θ̃)`, where `h̃ = (m!)⁻¹ ∑_σ h (· ∘ σ)` is the symmetrized
kernel, `θ̃ = E h̃` and `h̃₁ = hoeffdingProj μ h̃ 1` is its first projection.

The U-statistic only sees `h̃` (it averages over all injective index maps), so building the
projection, including its centring, from `h̃` makes this the projection of `uStatistic h` onto
sums of functions of single observations for an arbitrary, not necessarily symmetric, kernel.
In the usual regime where `h` is integrable, `E h̃ = E h`; Lean's totalized integral can differ
when `h` itself is not integrable, which is why the centring is `E h̃`. For a symmetric kernel
`h̃ = h` and this is `θ + (m / n) ∑_{i} (h₁(x_i) - θ)` with `θ = E h`
(`hajekProjection_eq_of_symm`). The intended regime is `m ≤ n`; for `m > n` the U-statistic is
`0` by convention and this is not its projection. -/
noncomputable def hajekProjection {α : Type*} [MeasurableSpace α] (μ : Measure α) {m n : ℕ}
    (h : (Fin m → α) → ℝ) (x : Fin n → α) : ℝ :=
  (∫ y, (m.factorial : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin m), h (y ∘ σ) ∂(Measure.pi fun _ => μ)) +
    (m : ℝ) / n * ∑ i, (hoeffdingProj μ
      (fun y => (m.factorial : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin m), h (y ∘ σ)) 1 (fun _ => x i) -
      ∫ y, (m.factorial : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin m), h (y ∘ σ) ∂(Measure.pi fun _ => μ))

/-- For a symmetric kernel the symmetrization in `hajekProjection` is the identity, so the
projection is `θ + (m / n) ∑_{i} (h₁(x_i) - θ)` with `h₁ = hoeffdingProj μ h 1`. -/
theorem hajekProjection_eq_of_symm {α : Type*} [MeasurableSpace α] (μ : Measure α) {m n : ℕ}
    {h : (Fin m → α) → ℝ} (hsymm : ∀ (σ : Equiv.Perm (Fin m)) y, h (y ∘ σ) = h y)
    (x : Fin n → α) :
    hajekProjection μ h x = (∫ y, h y ∂(Measure.pi fun _ => μ)) +
      (m : ℝ) / n * ∑ i, (hoeffdingProj μ h 1 (fun _ => x i) -
        ∫ y, h y ∂(Measure.pi fun _ => μ)) := by
  have hs : (fun y : Fin m → α => (m.factorial : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin m), h (y ∘ σ)) =
      h := by
    funext y
    simp_rw [hsymm]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast m.factorial_ne_zero), one_mul]
  rw [hajekProjection, hs]

private theorem integral_comp_of_measurePreserving_aesm {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {P : Measure X} {Q : Measure Y} {Φ : X → Y}
    (hΦ : MeasurePreserving Φ P Q) {F : Y → ℝ} (hF : AEStronglyMeasurable F Q) :
    ∫ x, F (Φ x) ∂P = ∫ y, F y ∂Q := by
  rw [← integral_map hΦ.aemeasurable (hΦ.map_eq.symm ▸ hF), hΦ.map_eq]

private theorem measurePreserving_coordinates_pair {α I J K : Type*} [MeasurableSpace α]
    [Fintype I] [Fintype J] [Fintype K] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : I ↪ K) (g : J ↪ K) (hfg : ∀ a b, f a ≠ g b) :
    MeasurePreserving (fun x : K → α => (x ∘ f, x ∘ g))
      (Measure.pi fun _ => μ) ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) := by
  let E : I ⊕ J ↪ K := ⟨Sum.elim f g, by
    rintro (a | a) (b | b) hab <;> dsimp only [Sum.elim_inl, Sum.elim_inr] at hab
    · exact congrArg Sum.inl (f.injective hab)
    · exact absurd hab (hfg a b)
    · exact absurd hab.symm (hfg b a)
    · exact congrArg Sum.inr (g.injective hab)⟩
  have hp := (measurePreserving_sumPiEquivProdPi (fun _ : I ⊕ J => μ)).comp
    (measurePreserving_coordinates μ E)
  convert hp using 1
  rfl

private theorem integral_mul_coordinates_pair {α I J K : Type*} [MeasurableSpace α]
    [Fintype I] [Fintype J] [Fintype K] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : I ↪ K) (g : J ↪ K) (hfg : ∀ a b, f a ≠ g b) {F : (I → α) → ℝ} {G : (J → α) → ℝ}
    (hF : AEStronglyMeasurable F (Measure.pi fun _ => μ))
    (hG : AEStronglyMeasurable G (Measure.pi fun _ => μ)) :
    ∫ x, F (x ∘ f) * G (x ∘ g) ∂(Measure.pi fun _ => μ) =
      (∫ y, F y ∂(Measure.pi fun _ => μ)) * ∫ y, G y ∂(Measure.pi fun _ => μ) := by
  have hm : AEStronglyMeasurable (fun p : (I → α) × (J → α) => F p.1 * G p.2)
      ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) :=
    (hF.comp_measurePreserving measurePreserving_fst).mul
      (hG.comp_measurePreserving measurePreserving_snd)
  rw [← integral_prod_mul]
  exact integral_comp_of_measurePreserving_aesm
    (measurePreserving_coordinates_pair μ f g hfg) hm

private theorem integral_sub_mul_integral_right_sub {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {H : A × B → ℝ}
    (hH : MemLp H 2 (μ.prod ν)) (c : ℝ) :
    ∫ p, (H p - c) * ((∫ z, H (p.1, z) ∂ν) - c) ∂(μ.prod ν) =
      ∫ y, ((∫ z, H (y, z) ∂ν) - c) ^ 2 ∂μ := by
  have hG : MemLp (fun p : A × B => (∫ z, H (p.1, z) ∂ν) - c) 2 (μ.prod ν) :=
    ((memLp_integral_right μ ν hH).comp_measurePreserving measurePreserving_fst).sub
      (memLp_const c)
  have hint : Integrable (fun p : A × B => (H p - c) * ((∫ z, H (p.1, z) ∂ν) - c))
      (μ.prod ν) := (hH.sub (memLp_const c)).integrable_mul hG
  rw [integral_prod _ hint]
  apply integral_congr_ae
  filter_upwards [(hH.integrable (by norm_num)).prod_right_ae] with y hy
  rw [integral_mul_const, integral_sub hy (integrable_const c), integral_const, probReal_univ,
    one_smul, sq]

private theorem memLp_integral_hoeffdingProj_one {α : Type*} [MeasurableSpace α] {m : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ] {h : (Fin m → α) → ℝ}
    (hh : MemLp h 2 (Measure.pi fun _ => μ)) :
    MemLp (hoeffdingProj μ h 1) 2 (Measure.pi fun _ : Fin 1 => μ) ∧
      ∫ y, hoeffdingProj μ h 1 y ∂(Measure.pi fun _ : Fin 1 => μ) =
        ∫ y, h y ∂(Measure.pi fun _ => μ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨a, rfl⟩ : ∃ a, h = fun _ => a :=
      ⟨h Fin.elim0, funext fun y => congrArg h (Subsingleton.elim _ _)⟩
    have he : hoeffdingProj μ (fun _ : Fin 0 → α => a) 1 = fun _ => a := by
      funext y
      simp [hoeffdingProj]
    rw [he]
    exact ⟨memLp_const a, by simp⟩
  · have hm1 : 1 ≤ m := hm
    have hp := measurePreserving_prefix_join hm1 μ
    have hH := hh.comp_measurePreserving hp
    exact ⟨memLp_integral_right _ _ hH, (integral_prod _ (hH.integrable (by norm_num))).symm.trans
      (integral_comp_of_measurePreserving_aesm hp hh.aestronglyMeasurable)⟩

/-- The first Hoeffding projection of a square-integrable kernel is square-integrable. -/
theorem memLp_hoeffdingProj_one {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1 ≤ m)
    {h : (Fin m → α) → ℝ} (hh : MemLp h 2 (Measure.pi fun _ => μ)) :
    MemLp (hoeffdingProj μ h 1) 2 (Measure.pi fun _ : Fin 1 => μ) := by
  let H : (Fin 1 → α) × (Fin (m - 1) → α) → ℝ := fun p =>
    h (fun j => if hj : (j : ℕ) < 1 then p.1 ⟨j, hj⟩
      else p.2 ⟨j - 1, by have := j.isLt; omega⟩)
  have hH : MemLp H 2 ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) :=
    hh.comp_measurePreserving (ProbabilityTheory.measurePreserving_prefix_join hm μ)
  have hproj : hoeffdingProj μ h 1
      = fun y => ∫ z, H (y, z) ∂(Measure.pi fun _ => μ) := by
    funext y
    simp [hoeffdingProj, H]
  rw [hproj]
  exact ProbabilityTheory.memLp_integral_right _ _ hH

private theorem integral_kernel_sub_mul_hoeffdingProj_one_sub {α : Type*}
    [MeasurableSpace α] {m n : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    {h : (Fin m → α) → ℝ} (hsymm : ∀ (σ : Equiv.Perm (Fin m)) y, h (y ∘ σ) = h y)
    (hh : MemLp h 2 (Measure.pi fun _ => μ)) (f : Fin m ↪ Fin n) (i : Fin n) :
    ∫ x, (h (x ∘ f) - ∫ y, h y ∂(Measure.pi fun _ => μ)) *
        (hoeffdingProj μ h 1 (fun _ => x i) - ∫ y, h y ∂(Measure.pi fun _ => μ))
        ∂(Measure.pi fun _ : Fin n => μ) =
      if i ∈ Finset.univ.map f then Var[hoeffdingProj μ h 1; Measure.pi fun _ : Fin 1 => μ]
      else 0 := by
  obtain ⟨hG, hGi⟩ := memLp_integral_hoeffdingProj_one μ hh
  split_ifs with hi
  · have hm : 1 ≤ m := by
      obtain ⟨k, -, -⟩ := Finset.mem_map.mp hi
      exact Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact k.elim0)
    let S : Finset (Fin n) := {i}
    let T : Finset (Fin n) := (Finset.univ.map f).erase i
    have hST : Disjoint S T := Finset.disjoint_singleton_left.mpr (Finset.notMem_erase i _)
    have hR : S ∪ T = Finset.univ.map f := by
      rw [← Finset.insert_eq, Finset.insert_erase hi]
    have hTc : T.card = m - 1 := by
      rw [Finset.card_erase_of_mem hi, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    let eS : Fin 1 ≃ S := (Finset.equivFinOfCardEq (Finset.card_singleton i)).symm
    let eT : Fin (m - 1) ≃ T := (Finset.equivFinOfCardEq hTc).symm
    let fS : Fin 1 ↪ Fin n := eS.toEmbedding.trans (Function.Embedding.subtype _)
    let fT : Fin (m - 1) ↪ Fin n := eT.toEmbedding.trans (Function.Embedding.subtype _)
    have hfS (k : Fin 1) : fS k = i := Finset.mem_singleton.mp (eS k).property
    have hdisj : ∀ a b, fS a ≠ fT b := fun a b hab => by
      have hab' : (eS a : Fin n) = eT b := hab
      exact Finset.disjoint_left.mp hST (eS a).property (hab' ▸ (eT b).property)
    let J : (Fin 1 → α) × (Fin (m - 1) → α) → (Fin m → α) := fun p j =>
      if hj : (j : ℕ) < 1 then p.1 ⟨j, hj⟩ else p.2 ⟨j - 1, by have := j.isLt; omega⟩
    have hpj : MeasurePreserving J ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))
        (Measure.pi fun _ => μ) := measurePreserving_prefix_join hm μ
    have hH : MemLp (fun p => h (J p)) 2
        ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) :=
      hh.comp_measurePreserving hpj
    let F : (Fin 1 → α) × (Fin (m - 1) → α) → ℝ := fun p =>
      (h (J p) - ∫ y, h y ∂(Measure.pi fun _ => μ)) *
        ((∫ z, h (J (p.1, z)) ∂(Measure.pi fun _ => μ)) - ∫ y, h y ∂(Measure.pi fun _ => μ))
    have hF : AEStronglyMeasurable F ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) :=
      ((hH.sub (memLp_const _)).integrable_mul
        (((memLp_integral_right _ _ hH).comp_measurePreserving measurePreserving_fst).sub
          (memLp_const _))).aestronglyMeasurable
    have hpt (x : Fin n → α) :
        (h (x ∘ f) - ∫ y, h y ∂(Measure.pi fun _ => μ)) *
          (hoeffdingProj μ h 1 (fun _ => x i) - ∫ y, h y ∂(Measure.pi fun _ => μ)) =
        F (x ∘ fS, x ∘ fT) := by
      have h1 : (fun _ : Fin 1 => x i) = x ∘ fS :=
        funext fun k => by rw [Function.comp_apply, hfS k]
      rw [reorder_selection hm f S T hST hR eS eT h hsymm x, h1]
      rfl
    calc _ = ∫ x, F (x ∘ fS, x ∘ fT) ∂(Measure.pi fun _ => μ) :=
          integral_congr_ae (Eventually.of_forall hpt)
      _ = ∫ p, F p ∂((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) :=
          integral_comp_of_measurePreserving_aesm
            (measurePreserving_coordinates_pair μ fS fT hdisj) hF
      _ = ∫ y, ((∫ z, h (J (y, z)) ∂(Measure.pi fun _ => μ)) -
            ∫ y, h y ∂(Measure.pi fun _ => μ)) ^ 2 ∂(Measure.pi fun _ => μ) :=
          integral_sub_mul_integral_right_sub _ _ hH _
      _ = _ := by
          rw [variance_eq_integral hG.aestronglyMeasurable.aemeasurable, hGi]
          rfl
  · let g : Fin 1 ↪ Fin n := ⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩
    have hdisj : ∀ a b, f a ≠ g b := fun a _ hab =>
      hi (Finset.mem_map.mpr ⟨a, Finset.mem_univ _, hab⟩)
    have hF : AEStronglyMeasurable (fun w : Fin m → α => h w - ∫ y, h y ∂(Measure.pi fun _ => μ))
        (Measure.pi fun _ => μ) := (hh.sub (memLp_const _)).aestronglyMeasurable
    have hG' : AEStronglyMeasurable
        (fun w : Fin 1 → α => hoeffdingProj μ h 1 w - ∫ y, h y ∂(Measure.pi fun _ => μ))
        (Measure.pi fun _ => μ) := (hG.sub (memLp_const _)).aestronglyMeasurable
    refine (integral_mul_coordinates_pair μ f g hdisj hF hG').trans ?_
    rw [integral_sub (hh.integrable (by norm_num)) (integrable_const _), integral_const,
      probReal_univ, one_smul, sub_self, zero_mul]

private theorem sum_ite_mem_map_mul {m n : ℕ} (i : Fin n) :
    (∑ f : Fin m ↪ Fin n, if i ∈ Finset.univ.map f then (1 : ℝ) else 0) * n =
      m * n.descFactorial m := by
  have hsw (j : Fin n) :
      (∑ f : Fin m ↪ Fin n, if j ∈ Finset.univ.map f then (1 : ℝ) else 0) =
        ∑ f : Fin m ↪ Fin n, if i ∈ Finset.univ.map f then (1 : ℝ) else 0 := by
    refine Fintype.sum_equiv (Equiv.embeddingCongr (Equiv.refl _) (Equiv.swap i j)) _ _
      (fun f => ?_)
    simp [Finset.mem_map, Equiv.swap_apply_eq_iff]
  have htot : ∑ j : Fin n, (∑ f : Fin m ↪ Fin n,
      if j ∈ Finset.univ.map f then (1 : ℝ) else 0) = m * n.descFactorial m := by
    have h1 (f : Fin m ↪ Fin n) :
        (∑ j : Fin n, if j ∈ Finset.univ.map f then (1 : ℝ) else 0) = m := by
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_map,
        Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun f _ => h1 f), Finset.sum_const,
      Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul, mul_comm]
  rw [← htot, Finset.sum_congr rfl (fun j _ => hsw j), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_comm]

/-- **Covariance of a U-statistic with one first-order projection term.** -/
theorem integral_uStatistic_sub_mul_hoeffdingProj_one_sub {α : Type*} [MeasurableSpace α]
    {m n : ℕ} (hmn : m ≤ n) (μ : Measure α) [IsProbabilityMeasure μ]
    {h : (Fin m → α) → ℝ} (hsymm : ∀ (σ : Equiv.Perm (Fin m)) y, h (y ∘ σ) = h y)
    (hh : MemLp h 2 (Measure.pi fun _ => μ)) (i : Fin n) :
    ∫ x, (uStatistic h x - ∫ y, h y ∂(Measure.pi fun _ => μ)) *
        (hoeffdingProj μ h 1 (fun _ => x i) - ∫ y, h y ∂(Measure.pi fun _ => μ))
        ∂(Measure.pi fun _ : Fin n => μ) =
      (m : ℝ) / n * Var[hoeffdingProj μ h 1; Measure.pi fun _ : Fin 1 => μ] := by
  obtain ⟨hG, -⟩ := memLp_integral_hoeffdingProj_one μ hh
  have hD : (n.descFactorial m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hmn).ne'
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Fin.pos i).ne'
  let g : Fin 1 ↪ Fin n := ⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩
  have hY : MemLp (fun x : Fin n → α =>
      hoeffdingProj μ h 1 (fun _ => x i) - ∫ y, h y ∂(Measure.pi fun _ => μ)) 2
      (Measure.pi fun _ => μ) :=
    (hG.comp_measurePreserving (measurePreserving_coordinates μ g)).sub (memLp_const _)
  have hX (f : Fin m ↪ Fin n) : MemLp (fun x : Fin n → α =>
      h (x ∘ f) - ∫ y, h y ∂(Measure.pi fun _ => μ)) 2 (Measure.pi fun _ => μ) :=
    (hh.comp_measurePreserving (measurePreserving_coordinates μ f)).sub (memLp_const _)
  have hU (x : Fin n → α) : uStatistic h x - ∫ y, h y ∂(Measure.pi fun _ => μ) =
      (∑ f : Fin m ↪ Fin n, (h (x ∘ f) - ∫ y, h y ∂(Measure.pi fun _ => μ))) /
        n.descFactorial m := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq,
      Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, uStatistic, sub_div,
      mul_div_cancel_left₀ _ hD]
  have hc := sum_ite_mem_map_mul (m := m) i
  calc _ = ∫ x, (∑ f : Fin m ↪ Fin n, (h (x ∘ f) - ∫ y, h y ∂(Measure.pi fun _ => μ)) *
          (hoeffdingProj μ h 1 (fun _ => x i) - ∫ y, h y ∂(Measure.pi fun _ => μ))) /
            n.descFactorial m ∂(Measure.pi fun _ => μ) := by
        congr 1
        funext x
        rw [hU, div_mul_eq_mul_div, Finset.sum_mul]
    _ = (∑ f : Fin m ↪ Fin n, ∫ x, (h (x ∘ f) - ∫ y, h y ∂(Measure.pi fun _ => μ)) *
          (hoeffdingProj μ h 1 (fun _ => x i) - ∫ y, h y ∂(Measure.pi fun _ => μ))
            ∂(Measure.pi fun _ => μ)) / n.descFactorial m := by
        rw [integral_div, integral_finsetSum]
        intro f _
        exact (hX f).integrable_mul hY
    _ = (∑ f : Fin m ↪ Fin n, if i ∈ Finset.univ.map f then (1 : ℝ) else 0) *
          Var[hoeffdingProj μ h 1; Measure.pi fun _ : Fin 1 => μ] / n.descFactorial m := by
        rw [Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl (fun f _ => ?_)
        rw [integral_kernel_sub_mul_hoeffdingProj_one_sub μ hsymm hh f i, ite_mul, one_mul,
          zero_mul]
    _ = _ := by
        field_simp
        linear_combination Var[hoeffdingProj μ h 1; Measure.pi fun _ : Fin 1 => μ] * hc

/-- **Hájek projection, L² identity.** -/
theorem integral_sq_uStatistic_sub_hajekProjection {α : Type*} [MeasurableSpace α]
    {m n : ℕ} (hmn : m ≤ n) (μ : Measure α) [IsProbabilityMeasure μ]
    {h : (Fin m → α) → ℝ} (hsymm : ∀ (σ : Equiv.Perm (Fin m)) y, h (y ∘ σ) = h y)
    (hh : MemLp h 2 (Measure.pi fun _ => μ)) :
    ∫ x, (uStatistic h x - hajekProjection μ h x) ^ 2 ∂(Measure.pi fun _ : Fin n => μ) =
      Var[uStatistic h; Measure.pi fun _ : Fin n => μ] -
        (m : ℝ) ^ 2 * Var[hoeffdingProj μ h 1; Measure.pi fun _ : Fin 1 => μ] / n := by
  obtain ⟨hG, hGi⟩ := memLp_integral_hoeffdingProj_one μ hh
  let g : Fin n → (Fin 1 ↪ Fin n) := fun i => ⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩
  have hY (i : Fin n) : MemLp (fun x : Fin n → α =>
      hoeffdingProj μ h 1 (fun _ => x i) - ∫ y, h y ∂(Measure.pi fun _ => μ)) 2
      (Measure.pi fun _ => μ) :=
    (hG.comp_measurePreserving (measurePreserving_coordinates μ (g i))).sub (memLp_const _)
  have hUm : MemLp (uStatistic h) 2 (Measure.pi fun _ : Fin n => μ) := by
    have hfun : uStatistic h = fun x : Fin n → α =>
        (∑ f : Fin m ↪ Fin n, h (x ∘ f)) * ((n.descFactorial m : ℝ)⁻¹) := by
      funext x
      rw [uStatistic, div_eq_mul_inv]
    rw [hfun]
    exact (memLp_finsetSum Finset.univ (fun f _ =>
      hh.comp_measurePreserving (measurePreserving_coordinates μ f))).mul_const _
  have hA : MemLp (fun x => uStatistic h x - ∫ y, h y ∂(Measure.pi fun _ => μ)) 2
      (Measure.pi fun _ : Fin n => μ) := hUm.sub (memLp_const _)
  have hB : MemLp (fun x : Fin n → α => ∑ i, (hoeffdingProj μ h 1 (fun _ => x i) -
      ∫ y, h y ∂(Measure.pi fun _ => μ))) 2 (Measure.pi fun _ => μ) :=
    memLp_finsetSum _ (fun i _ => hY i)
  have hVar : Var[uStatistic h; Measure.pi fun _ : Fin n => μ] =
      ∫ x, (uStatistic h x - ∫ y, h y ∂(Measure.pi fun _ => μ)) ^ 2
        ∂(Measure.pi fun _ : Fin n => μ) := by
    rw [variance_eq_integral hUm.aestronglyMeasurable.aemeasurable,
      integral_uStatistic hmn μ (hh.integrable (by norm_num))]
  have hAB : ∫ x, (uStatistic h x - ∫ y, h y ∂(Measure.pi fun _ => μ)) *
      ∑ i, (hoeffdingProj μ h 1 (fun _ => x i) - ∫ y, h y ∂(Measure.pi fun _ => μ))
        ∂(Measure.pi fun _ : Fin n => μ) =
      n * ((m : ℝ) / n * Var[hoeffdingProj μ h 1; Measure.pi fun _ : Fin 1 => μ]) := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum]
    · simp_rw [integral_uStatistic_sub_mul_hoeffdingProj_one_sub hmn μ hsymm hh]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · intro i _
      exact hA.integrable_mul (hY i)
  have hF : AEStronglyMeasurable (fun w : Fin 1 → α => hoeffdingProj μ h 1 w -
      ∫ y, h y ∂(Measure.pi fun _ => μ)) (Measure.pi fun _ => μ) :=
    (hG.sub (memLp_const _)).aestronglyMeasurable
  have hYY (i j : Fin n) :
      ∫ x, (hoeffdingProj μ h 1 (fun _ => x i) - ∫ y, h y ∂(Measure.pi fun _ => μ)) *
        (hoeffdingProj μ h 1 (fun _ => x j) - ∫ y, h y ∂(Measure.pi fun _ => μ))
          ∂(Measure.pi fun _ : Fin n => μ) =
        if i = j then Var[hoeffdingProj μ h 1; Measure.pi fun _ : Fin 1 => μ] else 0 := by
    split_ifs with hij
    · subst hij
      have hF2 : AEStronglyMeasurable (fun w : Fin 1 → α => (hoeffdingProj μ h 1 w -
          ∫ y, h y ∂(Measure.pi fun _ => μ)) ^ 2) (Measure.pi fun _ => μ) := hF.pow 2
      rw [variance_eq_integral hG.aestronglyMeasurable.aemeasurable, hGi]
      simp_rw [← sq]
      exact integral_comp_of_measurePreserving_aesm (measurePreserving_coordinates μ (g i)) hF2
    · refine (integral_mul_coordinates_pair μ (g i) (g j) (fun _ _ hab => hij hab) hF hF).trans ?_
      rw [integral_sub (hG.integrable (by norm_num)) (integrable_const _), integral_const,
        probReal_univ, one_smul, hGi, sub_self, zero_mul]
  have hI (i j : Fin n) : Integrable (fun x : Fin n → α =>
      (hoeffdingProj μ h 1 (fun _ => x i) - ∫ y, h y ∂(Measure.pi fun _ => μ)) *
        (hoeffdingProj μ h 1 (fun _ => x j) - ∫ y, h y ∂(Measure.pi fun _ => μ)))
      (Measure.pi fun _ => μ) := (hY i).integrable_mul (hY j)
  have hBB : ∫ x, (∑ i, (hoeffdingProj μ h 1 (fun _ => x i) -
      ∫ y, h y ∂(Measure.pi fun _ => μ))) ^ 2 ∂(Measure.pi fun _ : Fin n => μ) =
      n * Var[hoeffdingProj μ h 1; Measure.pi fun _ : Fin 1 => μ] := by
    simp_rw [sq, Finset.sum_mul_sum]
    rw [integral_finsetSum]
    · rw [Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun j _ => hI i j))]
      simp_rw [hYY, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · intro i _
      exact integrable_finsetSum _ (fun j _ => hI i j)
  have hpt (x : Fin n → α) : (uStatistic h x - hajekProjection μ h x) ^ 2 =
      (uStatistic h x - ∫ y, h y ∂(Measure.pi fun _ => μ)) ^ 2 -
        2 * ((m : ℝ) / n) * ((uStatistic h x - ∫ y, h y ∂(Measure.pi fun _ => μ)) *
          ∑ i, (hoeffdingProj μ h 1 (fun _ => x i) - ∫ y, h y ∂(Measure.pi fun _ => μ))) +
        ((m : ℝ) / n) ^ 2 * (∑ i, (hoeffdingProj μ h 1 (fun _ => x i) -
          ∫ y, h y ∂(Measure.pi fun _ => μ))) ^ 2 := by
    rw [hajekProjection_eq_of_symm μ hsymm]
    ring
  have i1 : Integrable (fun x => (uStatistic h x - ∫ y, h y ∂(Measure.pi fun _ => μ)) ^ 2)
      (Measure.pi fun _ : Fin n => μ) := hA.integrable_sq
  have i2 : Integrable (fun x => 2 * ((m : ℝ) / n) *
      ((uStatistic h x - ∫ y, h y ∂(Measure.pi fun _ => μ)) *
        ∑ i, (hoeffdingProj μ h 1 (fun _ => x i) - ∫ y, h y ∂(Measure.pi fun _ => μ))))
      (Measure.pi fun _ : Fin n => μ) := (hA.integrable_mul hB).const_mul _
  have i12 : Integrable (fun x => (uStatistic h x - ∫ y, h y ∂(Measure.pi fun _ => μ)) ^ 2 -
      2 * ((m : ℝ) / n) * ((uStatistic h x - ∫ y, h y ∂(Measure.pi fun _ => μ)) *
        ∑ i, (hoeffdingProj μ h 1 (fun _ => x i) - ∫ y, h y ∂(Measure.pi fun _ => μ))))
      (Measure.pi fun _ : Fin n => μ) := i1.sub i2
  have i3 : Integrable (fun x => ((m : ℝ) / n) ^ 2 * (∑ i, (hoeffdingProj μ h 1 (fun _ => x i) -
      ∫ y, h y ∂(Measure.pi fun _ => μ))) ^ 2) (Measure.pi fun _ : Fin n => μ) :=
    hB.integrable_sq.const_mul _
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add i12 i3, integral_sub i1 i2,
    integral_const_mul, integral_const_mul, hAB, hBB, ← hVar]
  rcases eq_or_ne (n : ℝ) 0 with hn | hn
  · simp [hn]
  · field_simp
    ring

private theorem tendsto_choose_sub_div_pow (a k : ℕ) :
    Tendsto (fun n : ℕ => (((n - a).choose k : ℕ) : ℝ) / (n : ℝ) ^ k) atTop
      (𝓝 ((k.factorial : ℝ)⁻¹)) := by
  have hlin : Tendsto (fun n : ℕ => ((n - a + 1 - k : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have h2 : Tendsto (fun n : ℕ => 1 + (1 - (a : ℝ) - k) / n) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (1 - (a : ℝ) - k))
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop (a + k + 1)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      positivity
    rw [show n - a + 1 - k = n + 1 - (a + k) by omega, Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  have hlow : Tendsto (fun n : ℕ => (((n - a + 1 - k : ℕ) : ℝ) / n) ^ k / k.factorial) atTop
      (𝓝 ((k.factorial : ℝ)⁻¹)) := by
    simpa [one_div] using (hlin.pow k).div_const (k.factorial : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    calc (((n - a + 1 - k : ℕ) : ℝ) / n) ^ k / k.factorial
        = (((n - a + 1 - k : ℕ) : ℝ) ^ k / k.factorial) / (n : ℝ) ^ k := by
          rw [div_pow]
          ring
      _ ≤ (((n - a).choose k : ℕ) : ℝ) / (n : ℝ) ^ k := by
          gcongr
          exact Nat.pow_le_choose k (n - a)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) ^ k := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    rw [div_le_iff₀ hn0]
    calc (((n - a).choose k : ℕ) : ℝ) ≤ ((n - a : ℕ) : ℝ) ^ k / k.factorial :=
          Nat.choose_le_pow_div k (n - a)
      _ ≤ (n : ℝ) ^ k / k.factorial := by
          gcongr
          exact_mod_cast Nat.sub_le n a
      _ = (k.factorial : ℝ)⁻¹ * (n : ℝ) ^ k := by ring

private theorem tendsto_mul_choose_div_choose {m c : ℕ} (hc : 1 ≤ c) (hcm : c ≤ m) :
    Tendsto (fun n : ℕ => (n : ℝ) * (m.choose c : ℝ) * ((n - m).choose (m - c) : ℝ) /
      (n.choose m : ℝ)) atTop (𝓝 (if c = 1 then (m : ℝ) ^ 2 else 0)) := by
  have R1 := tendsto_choose_sub_div_pow m (m - c)
  have R2 := tendsto_choose_sub_div_pow 0 m
  simp only [Nat.sub_zero] at R2
  have hm0 : ((m.factorial : ℝ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast (Nat.factorial_pos m).ne')
  have Q : Tendsto (fun n : ℕ => (n : ℝ) / (n : ℝ) ^ c) atTop
      (𝓝 (if c = 1 then 1 else 0)) := by
    split_ifs with h1
    · subst h1
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (n : ℝ) ≠ 0 := by
        have : 0 < n := by omega
        positivity
      field_simp
    · obtain ⟨d, rfl⟩ : ∃ d, c = d + 2 := ⟨c - 2, by omega⟩
      have hT := tendsto_inv_atTop_zero.comp
        ((tendsto_pow_atTop (by omega : d + 1 ≠ 0)).comp (tendsto_natCast_atTop_atTop (R := ℝ)))
      refine hT.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (n : ℝ) ≠ 0 := by
        have : 0 < n := by omega
        positivity
      simp only [Function.comp_apply]
      rw [show (n : ℝ) ^ (d + 2) = (n : ℝ) ^ (d + 1) * n by ring]
      field_simp
  have hlim := ((R1.const_mul (m.choose c : ℝ)).mul (R2.inv₀ hm0)).mul Q
  have hval : (m.choose c : ℝ) * ((m - c).factorial : ℝ)⁻¹ * ((m.factorial : ℝ)⁻¹)⁻¹ *
      (if c = 1 then 1 else 0) = if c = 1 then (m : ℝ) ^ 2 else 0 := by
    split_ifs with h1
    · subst h1
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.choose_one_right, Nat.add_sub_cancel, Nat.factorial_succ, inv_inv,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_one]
      have : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
      field_simp
    · simp
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (m + 1)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    have : 0 < n := by omega
    positivity
  have hC : (n.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [show (n : ℝ) ^ m = (n : ℝ) ^ (m - c) * (n : ℝ) ^ c by
    rw [← pow_add, Nat.sub_add_cancel hcm]]
  field_simp

/-- **Asymptotic variance of a U-statistic** (Hoeffding 1948, §5). -/
theorem tendsto_mul_variance_uStatistic {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {m : ℕ} {h : (Fin m → α) → ℝ}
    (hsymm : ∀ (σ : Equiv.Perm (Fin m)) y, h (y ∘ σ) = h y)
    (hh : MemLp h 2 (Measure.pi fun _ => μ)) :
    Tendsto (fun n : ℕ => (n : ℝ) * Var[uStatistic h; Measure.pi fun _ : Fin n => μ]) atTop
      (𝓝 ((m : ℝ) ^ 2 * Var[hoeffdingProj μ h 1; Measure.pi fun _ : Fin 1 => μ])) := by
  have hev : (fun n : ℕ => ∑ c ∈ Finset.Icc 1 m,
      (n : ℝ) * (m.choose c : ℝ) * ((n - m).choose (m - c) : ℝ) / (n.choose m : ℝ) *
        Var[hoeffdingProj μ h c; Measure.pi fun _ : Fin c => μ]) =ᶠ[atTop]
      fun n : ℕ => (n : ℝ) * Var[uStatistic h; Measure.pi fun _ : Fin n => μ] := by
    filter_upwards [eventually_ge_atTop m] with n hn
    rw [variance_uStatistic hn μ hsymm hh, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  refine Tendsto.congr' hev ?_
  have hlim := tendsto_finsetSum (Finset.Icc 1 m) (fun c hc =>
    (tendsto_mul_choose_div_choose (Finset.mem_Icc.mp hc).1 (Finset.mem_Icc.mp hc).2).mul_const
      (Var[hoeffdingProj μ h c; Measure.pi fun _ : Fin c => μ]))
  convert hlim using 2
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  split_ifs with h1
  · rfl
  · have hm : m = 0 := by
      simp only [Finset.mem_Icc, le_refl, true_and, not_le] at h1
      omega
    subst hm
    simp

/-- **Hájek projection remainder has squared L² norm `o(1/n)`**: `n E[(U - Ĥ)²] → 0`, i.e. the
remainder is `o(n^{-1/2})` in L². -/
theorem tendsto_mul_integral_sq_uStatistic_sub_hajekProjection {α : Type*}
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] {m : ℕ}
    {h : (Fin m → α) → ℝ} (hsymm : ∀ (σ : Equiv.Perm (Fin m)) y, h (y ∘ σ) = h y)
    (hh : MemLp h 2 (Measure.pi fun _ => μ)) :
    Tendsto (fun n : ℕ => (n : ℝ) *
        ∫ x, (uStatistic h x - hajekProjection μ h x) ^ 2 ∂(Measure.pi fun _ : Fin n => μ))
      atTop (𝓝 0) := by
  have h3 := (tendsto_mul_variance_uStatistic μ hsymm hh).sub_const
    ((m : ℝ) ^ 2 * Var[hoeffdingProj μ h 1; Measure.pi fun _ : Fin 1 => μ])
  rw [sub_self] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (max m 1)] with n hn
  rw [integral_sq_uStatistic_sub_hajekProjection (le_of_max_le_left hn) μ hsymm hh]
  have hn0 : (n : ℝ) ≠ 0 := by
    have := le_of_max_le_right hn
    positivity
  field_simp

end ProbabilityTheory
