/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Module
import Mathlib.Tactic.Positivity.Finset

/-!
# The discrete Hölder–Brascamp–Lieb inequality for subgroups of `ℤ^d`

Christ, Demmel, Knight, Scanlon and Yelick (*Communication lower bounds and optimal algorithms
for programs that reference arrays, Part 1*, arXiv:1308.0068, 2013, Theorem 3.2) characterise
the exponents `s ∈ [0, 1]^m` for which every finite set `E ⊆ ℤ^d` satisfies
`|E| ≤ ∏ⱼ |φⱼ(E)|^{sⱼ}`, for group homomorphisms `φⱼ : ℤ^d → ℤ^{dⱼ}`: exactly those with
`rank H ≤ ∑ⱼ sⱼ rank φⱼ(H)` for every subgroup `H ≤ ℤ^d`. This is the discrete Hölder–Brascamp–Lieb
(HBL) inequality behind their communication lower bound `Ω(|Z| / M^{s_HBL - 1})` for programs whose
array subscripts are affine in the loop indices (their Theorem 4.1). The three coordinate
projections `ℤ³ → ℤ²` with `s = (1/2, 1/2, 1/2)` give the discrete Loomis–Whitney inequality.

## Main results

* `rank_le_iff_card_le_prod`: the rank condition holds for every subgroup of `ℤ^d` if and only
  if the counting inequality holds for every nonempty finite subset of `ℤ^d`.

## Proof outline

The proof follows Section 3 of the source, where the inequality is deduced from its version for
vector spaces (Theorem 3.10 there).

* **From `ℤ^d` to `ℚ^d`.** Let `ψⱼ : ℚ^d → ℚ^{dⱼ}` be the `ℚ`-linear map with the integer matrix
  of `φⱼ`. For a subspace `W ≤ ℚ^d`, let `H` be the subgroup of integer vectors in `W`. Clearing
  denominators in a basis of `W` gives `dim W ≤ rank H`, and a basis of `φⱼ(H)` stays linearly
  independent over `ℚ`, so `rank φⱼ(H) ≤ dim ψⱼ(W)`. Hence the rank condition gives the dimension
  condition `dim W ≤ ∑ⱼ sⱼ dim ψⱼ(W)` for every subspace `W`.
* **Vector spaces.** Over any field, the dimension condition gives the multilinear inequality
  `∑_{x ∈ S} ∏ⱼ Fⱼ(ψⱼ x)^{sⱼ} ≤ ∏ⱼ (∑_{y ∈ ψⱼ(S)} Fⱼ(y))^{sⱼ}` for every nonempty finite set
  `S` and all functions `Fⱼ` that are positive at the points `ψⱼ x`, `x ∈ S`. The proof is by
  induction on the dimension. The admissible exponents form a compact convex polytope, and the
  exponents for which the inequality holds form a closed set that is convex by Hölder's
  inequality, so by the Krein–Milman theorem it suffices to treat the extreme points of the
  polytope. At an extreme point `s`, either some subspace `0 < W < V` is critical,
  `dim W = ∑ⱼ sⱼ dim ψⱼ(W)`, and the inequality factors through `W` and `V ⧸ W`; or `sₖ = 1`
  for some `k` with `ψₖ ≠ 0`, and one sums over the fibres of `ψₖ`, which are cosets of the
  smaller space `ker ψₖ`; or `V = 0`. Otherwise some `sᵢ` lies strictly between `0` and `1`,
  and a perturbation `s ± εv` stays in the polytope, which contradicts extremality. (The source
  instead shows that an extreme point without a critical subspace lies in `{0, 1}^m`, and treats
  that case directly.) Taking `Fⱼ = 1` and `S` the image of `E` in `ℚ^d` gives the counting
  inequality.
* **The converse.** For a subgroup `H` of rank `r` with basis `b₁, …, b_r`, the sets
  `{∑ᵢ aᵢ bᵢ : 0 ≤ aᵢ < N}` have `N^r` points, and their images under `φⱼ` have
  `O(N^{rank φⱼ(H)})` points, by the coordinates in a basis of `φⱼ(H)`. The counting inequality
  then gives `N^r ≤ B N^{∑ⱼ sⱼ rank φⱼ(H)}` for all `N ≥ 1`, and letting `N → ∞` gives the rank
  condition.
-/

@[expose] public section

open Module Finset

namespace MathlibExt.Combinatorics.DiscreteHolderBrascampLiebWanted

universe u v

/-! ### The inequality for vector spaces over a field -/

section Field

variable {K : Type*} [Field K] {m : ℕ}

section Datum

variable {V : Type u} [AddCommGroup V] [Module K V] {Vj : Fin m → Type v}
  [∀ j, AddCommGroup (Vj j)] [∀ j, Module K (Vj j)]

/-- The dimension condition of a vector-space Hölder–Brascamp–Lieb datum. -/
private def DimCond (ψ : ∀ j, V →ₗ[K] Vj j) (s : Fin m → ℝ) : Prop :=
  ∀ W : Submodule K V, (finrank K W : ℝ) ≤ ∑ j, s j * (finrank K (W.map (ψ j)) : ℝ)

open scoped Classical in
/-- The multilinear form of the inequality, for functions positive at the relevant points. -/
private def FunIneq (ψ : ∀ j, V →ₗ[K] Vj j) (s : Fin m → ℝ) : Prop :=
  ∀ (S : Finset V) (F : ∀ j, Vj j → ℝ), S.Nonempty → (∀ j, ∀ x ∈ S, 0 < F j (ψ j x)) →
    ∑ x ∈ S, ∏ j, F j (ψ j x) ^ s j ≤ ∏ j, (∑ y ∈ S.image (ψ j), F j y) ^ s j

/-- The polytope of admissible exponents. -/
private def polytope (ψ : ∀ j, V →ₗ[K] Vj j) : Set (Fin m → ℝ) :=
  {s | (∀ j, s j ∈ Set.Icc (0 : ℝ) 1) ∧ DimCond ψ s}

/-- Hölder's inequality for two nonnegative functions with weights `θ + η = 1`. -/
private theorem sum_rpow_mul_rpow_le {ι : Type*} (S : Finset ι) (u w : ι → ℝ)
    (hu : ∀ i ∈ S, 0 ≤ u i) (hw : ∀ i ∈ S, 0 ≤ w i) {θ η : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (h : θ + η = 1) :
    ∑ i ∈ S, u i ^ θ * w i ^ η ≤ (∑ i ∈ S, u i) ^ θ * (∑ i ∈ S, w i) ^ η := by
  rcases hθ.eq_or_lt with rfl | hθ'
  · obtain rfl : η = 1 := by linarith
    simp
  rcases hη.eq_or_lt with rfl | hη'
  · obtain rfl : θ = 1 := by linarith
    simp
  have hpq := Real.HolderConjugate.inv_inv hθ' hη' h
  have := Real.inner_le_Lp_mul_Lq_of_nonneg S hpq (f := fun i => u i ^ θ) (g := fun i => w i ^ η)
    (fun i hi => Real.rpow_nonneg (hu i hi) _) (fun i hi => Real.rpow_nonneg (hw i hi) _)
  simp only [one_div, inv_inv] at this
  convert this using 3
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Real.rpow_rpow_inv (hu i hi) hθ'.ne']
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Real.rpow_rpow_inv (hw i hi) hη'.ne']

open scoped Classical in
/-- The exponents for which the multilinear inequality holds form a convex set, by Hölder's
inequality. -/
private theorem funIneq_convex (ψ : ∀ j, V →ₗ[K] Vj j) :
    Convex ℝ {s | FunIneq ψ s} := by
  intro a ha b hb θ η hθ hη hθη S F hne hpos
  have hA : ∀ j, 0 < ∑ y ∈ S.image (ψ j), F j y := by
    intro j
    refine Finset.sum_pos (fun y hy => ?_) (hne.image _)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hpos j x hx
  have split : ∀ (c : Fin m → ℝ), (∀ j, 0 < c j) →
      ∏ j, c j ^ (θ • a + η • b) j = (∏ j, c j ^ a j) ^ θ * (∏ j, c j ^ b j) ^ η := by
    intro c hc
    rw [← Real.finsetProd_rpow _ _ (fun j _ => (Real.rpow_nonneg (hc j).le _)),
      ← Real.finsetProd_rpow _ _ (fun j _ => (Real.rpow_nonneg (hc j).le _)),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Real.rpow_mul (hc j).le, ← Real.rpow_mul (hc j).le, ← Real.rpow_add (hc j)]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf
  rw [Finset.sum_congr rfl fun x hx => split (fun j => F j (ψ j x)) (fun j => hpos j x hx),
    split _ hA]
  refine (sum_rpow_mul_rpow_le S _ _ (fun x _ => Finset.prod_nonneg fun j _ =>
    Real.rpow_nonneg (hpos j x ‹_›).le _) (fun x _ => Finset.prod_nonneg fun j _ =>
    Real.rpow_nonneg (hpos j x ‹_›).le _) hθ hη hθη).trans ?_
  exact mul_le_mul
    (Real.rpow_le_rpow (Finset.sum_nonneg fun x hx => Finset.prod_nonneg fun j _ =>
      Real.rpow_nonneg (hpos j x hx).le _) (ha S F hne hpos) hθ)
    (Real.rpow_le_rpow (Finset.sum_nonneg fun x hx => Finset.prod_nonneg fun j _ =>
      Real.rpow_nonneg (hpos j x hx).le _) (hb S F hne hpos) hη)
    (Real.rpow_nonneg (Finset.sum_nonneg fun x hx => Finset.prod_nonneg fun j _ =>
      Real.rpow_nonneg (hpos j x hx).le _) _)
    (Real.rpow_nonneg (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hA j).le _) _)

open scoped Classical in
/-- The exponents for which the multilinear inequality holds form a closed set: both sides are
continuous in the exponents, the bases being positive. -/
private theorem funIneq_isClosed (ψ : ∀ j, V →ₗ[K] Vj j) :
    IsClosed {s | FunIneq ψ s} := by
  simp only [FunIneq, Set.ofPred_forall]
  refine isClosed_iInter fun S => isClosed_iInter fun F => isClosed_iInter fun hne =>
    isClosed_iInter fun hpos => isClosed_le ?_ ?_
  · exact continuous_finsetSum _ fun x hx => continuous_finsetProd _ fun j _ =>
      continuous_const.rpow (continuous_apply j) fun _ => Or.inl (hpos j x hx).ne'
  · refine continuous_finsetProd _ fun j _ =>
      continuous_const.rpow (continuous_apply j) fun _ => Or.inl (ne_of_gt ?_)
    refine Finset.sum_pos (fun y hy => ?_) (hne.image _)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hpos j x hx

/-- The polytope of admissible exponents is compact. -/
private theorem polytope_isCompact (ψ : ∀ j, V →ₗ[K] Vj j) : IsCompact (polytope ψ) := by
  have hcl : IsClosed (polytope ψ) := by
    have : polytope ψ = (⋂ j, (fun s : Fin m → ℝ => s j) ⁻¹' Set.Icc 0 1) ∩
        ⋂ W : Submodule K V, {s | (finrank K W : ℝ) ≤
          ∑ j, s j * (finrank K (W.map (ψ j)) : ℝ)} := by
      ext s
      simp [polytope, DimCond]
    rw [this]
    exact (isClosed_iInter fun j => isClosed_Icc.preimage (continuous_apply j)).inter
      (isClosed_iInter fun W => isClosed_le continuous_const
        (continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const))
  refine (isCompact_Icc (a := (0 : Fin m → ℝ)) (b := 1)).of_isClosed_subset hcl ?_
  intro s hs
  exact ⟨fun j => (hs.1 j).1, fun j => (hs.1 j).2⟩

/-- The polytope of admissible exponents is convex. -/
private theorem polytope_convex (ψ : ∀ j, V →ₗ[K] Vj j) : Convex ℝ (polytope ψ) := by
  intro a ha b hb θ η hθ hη hθη
  refine ⟨fun j => ⟨?_, ?_⟩, fun W => ?_⟩
  · have := (ha.1 j).1
    have := (hb.1 j).1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    positivity
  · have := (ha.1 j).2
    have := (hb.1 j).2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  · have h1 := ha.2 W
    have h2 := hb.2 W
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum]
    nlinarith

/-- On the zero space the inequality holds for all exponents. -/
private theorem funIneq_of_finrank_eq_zero [FiniteDimensional K V] (ψ : ∀ j, V →ₗ[K] Vj j)
    (s : Fin m → ℝ) (hV : finrank K V = 0) : FunIneq ψ s := by
  classical
  intro S F hne hpos
  obtain ⟨x₀, hx₀⟩ := hne
  have hS : S = {x₀} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hx₀, fun x _ => ?_⟩
    rw [finrank_zero_iff_forall_zero.mp hV x, finrank_zero_iff_forall_zero.mp hV x₀]
  subst hS
  simp

open scoped Classical in
/-- If the inequality holds for the restriction of the datum to `U`, it holds for every finite
set contained in a coset of `U`. -/
private theorem funIneq_coset (ψ : ∀ j, V →ₗ[K] Vj j) {s : Fin m → ℝ} (U : Submodule K V)
    (hs : ∀ j, 0 ≤ s j) (hU : FunIneq (fun j => (ψ j).comp U.subtype) s)
    (S : Finset V) (F : ∀ j, Vj j → ℝ) (hne : S.Nonempty)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ U) (hpos : ∀ j, ∀ x ∈ S, 0 < F j (ψ j x)) :
    ∑ x ∈ S, ∏ j, F j (ψ j x) ^ s j ≤ ∏ j, (∑ y ∈ S.image (ψ j), F j y) ^ s j := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hinj : Set.InjOn (fun u : U => x₀ + (u : V)) ((fun u : U => x₀ + (u : V)) ⁻¹' ↑S) :=
    fun u _ u' _ h => Subtype.ext (add_left_cancel h)
  set T := S.preimage (fun u : U => x₀ + (u : V)) hinj
  have hT : ∀ u : U, u ∈ T ↔ x₀ + (u : V) ∈ S := fun u => Finset.mem_preimage
  have hTne : T.Nonempty := ⟨0, by simp [hT, hx₀]⟩
  set F' : ∀ j, Vj j → ℝ := fun j z => F j (ψ j x₀ + z)
  have hF' : ∀ j (u : U), F' j (((ψ j).comp U.subtype) u) = F j (ψ j (x₀ + u)) := by
    intro j u
    simp [F', map_add]
  have hpos' : ∀ j, ∀ u ∈ T, 0 < F' j (((ψ j).comp U.subtype) u) := by
    intro j u hu
    rw [hF']
    exact hpos j _ ((hT u).mp hu)
  have h1 := hU T F' hTne hpos'
  have hL : ∑ u ∈ T, ∏ j, F' j (((ψ j).comp U.subtype) u) ^ s j =
      ∑ x ∈ S, ∏ j, F j (ψ j x) ^ s j := by
    simp_rw [hF']
    refine Finset.sum_preimage (fun u : U => x₀ + (u : V)) S hinj
      (fun x => ∏ j, F j (ψ j x) ^ s j) fun x hx hxr => ?_
    exact absurd ⟨⟨x - x₀, hS x hx x₀ hx₀⟩, by simp⟩ hxr
  have hR : ∀ j, ∑ z ∈ T.image ((ψ j).comp U.subtype), F' j z ≤
      ∑ y ∈ S.image (ψ j), F j y := by
    intro j
    rw [← Finset.sum_image (s := T.image ((ψ j).comp U.subtype)) (g := fun z => ψ j x₀ + z)
      (fun _ _ _ _ h => add_left_cancel h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y hy _ => ?_
    · intro y hy
      simp only [Finset.mem_image] at hy ⊢
      obtain ⟨_, ⟨u, hu, rfl⟩, rfl⟩ := hy
      exact ⟨x₀ + u, (hT u).mp hu, by simp [map_add]⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (hpos j x hx).le
  rw [← hL]
  refine h1.trans (Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg ?_ _)
    fun j _ => Real.rpow_le_rpow ?_ (hR j) (hs j))
  all_goals
    refine Finset.sum_nonneg fun z hz => ?_
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    exact (hpos' j u hu).le

open scoped Classical in
/-- **Factorisation through a subspace.** The inequality for the restriction of the datum to `W`
and for the induced datum on `V ⧸ W` gives the inequality on `V`. -/
private theorem funIneq_of_quotient (ψ : ∀ j, V →ₗ[K] Vj j) {s : Fin m → ℝ}
    (W : Submodule K V) (hs : ∀ j, 0 ≤ s j)
    (hW : FunIneq (fun j => (ψ j).comp W.subtype) s)
    (hQ : FunIneq (fun j => W.mapQ (W.map (ψ j)) (ψ j) (Submodule.le_comap_map (ψ j) W)) s) :
    FunIneq ψ s := by
  intro S F hne hpos
  set π := W.mkQ
  set ψq := fun j => W.mapQ (W.map (ψ j)) (ψ j) (Submodule.le_comap_map (ψ j) W)
  have hcomm : ∀ j x, ψq j (π x) = (W.map (ψ j)).mkQ (ψ j x) := fun j x => rfl
  set Φ : ∀ j, Vj j ⧸ W.map (ψ j) → ℝ := fun j e =>
    ∑ y ∈ S.image (ψ j) with (W.map (ψ j)).mkQ y = e, F j y
  have hΦ : ∀ j, ∀ x ∈ S, F j (ψ j x) ≤ Φ j (ψq j (π x)) := by
    intro j x hx
    refine Finset.single_le_sum (f := F j) (fun y hy => ?_) ?_
    · obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hy).1
      exact (hpos j x' hx').le
    · exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hx, (hcomm j x).symm⟩
  have hpos' : ∀ j, ∀ c ∈ S.image π, 0 < Φ j (ψq j c) := by
    intro j c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    exact (hpos j x hx).trans_le (hΦ j x hx)
  have hfib : ∀ c ∈ S.image π, ∑ x ∈ S with π x = c, ∏ j, F j (ψ j x) ^ s j ≤
      ∏ j, Φ j (ψq j c) ^ s j := by
    intro c hc
    obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hc
    have hfne : (S.filter fun x => π x = π x₁).Nonempty := ⟨x₁, by simp [hx₁]⟩
    refine (funIneq_coset ψ W hs hW _ F hfne ?_ fun j x hx => hpos j x
      (Finset.mem_filter.mp hx).1).trans ?_
    · intro x hx y hy
      simp only [Finset.mem_filter] at hx hy
      have : π x = π y := hx.2.trans hy.2.symm
      exact (Submodule.Quotient.eq W).mp this
    · refine Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg ?_ _)
        fun j _ => Real.rpow_le_rpow ?_ ?_ (hs j)
      · refine Finset.sum_nonneg fun y hy => ?_
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact (hpos j x (Finset.mem_filter.mp hx).1).le
      · refine Finset.sum_nonneg fun y hy => ?_
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact (hpos j x (Finset.mem_filter.mp hx).1).le
      · refine Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) fun y hy _ => ?_
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          simp only [Finset.mem_filter] at hx
          refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hx.1, ?_⟩
          rw [← hcomm, hx.2]
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hy).1
          exact (hpos j x hx).le
  have hsum : ∀ j, ∑ e ∈ (S.image π).image (ψq j), Φ j e = ∑ y ∈ S.image (ψ j), F j y := by
    intro j
    refine Finset.sum_fiberwise_of_maps_to (fun y hy => ?_) _
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨π x, Finset.mem_image_of_mem _ hx, hcomm j x⟩
  calc ∑ x ∈ S, ∏ j, F j (ψ j x) ^ s j
      = ∑ c ∈ S.image π, ∑ x ∈ S with π x = c, ∏ j, F j (ψ j x) ^ s j :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem π hx) _).symm
    _ ≤ ∑ c ∈ S.image π, ∏ j, Φ j (ψq j c) ^ s j := Finset.sum_le_sum hfib
    _ ≤ ∏ j, (∑ e ∈ (S.image π).image (ψq j), Φ j e) ^ s j :=
        hQ (S.image π) Φ (hne.image π) hpos'
    _ = ∏ j, (∑ y ∈ S.image (ψ j), F j y) ^ s j := by simp_rw [hsum]

open scoped Classical in
/-- If `s k = 1`, the inequality on `ker ψₖ` gives the inequality on `V`, by summing over the
fibres of `ψₖ`. -/
private theorem funIneq_of_fiber (ψ : ∀ j, V →ₗ[K] Vj j) {s : Fin m → ℝ} (k : Fin m)
    (hk : s k = 1) (hs : ∀ j, 0 ≤ s j)
    (hU : FunIneq (fun j => (ψ j).comp (LinearMap.ker (ψ k)).subtype) s) :
    FunIneq ψ s := by
  intro S F hne hpos
  set A : Fin m → ℝ := fun j => ∑ y ∈ S.image (ψ j), F j y
  have hA : ∀ j, 0 ≤ A j := by
    intro j
    refine Finset.sum_nonneg fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (hpos j x hx).le
  set R := ∏ j ∈ Finset.univ.erase k, A j ^ s j
  have hR : 0 ≤ R := Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hA j) _
  have hfib : ∀ c ∈ S.image (ψ k), ∑ x ∈ S with ψ k x = c, ∏ j, F j (ψ j x) ^ s j ≤
      F k c * R := by
    intro c hc
    obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hc
    have hfne : (S.filter fun x => ψ k x = ψ k x₁).Nonempty := ⟨x₁, by simp [hx₁]⟩
    refine (funIneq_coset ψ _ hs hU _ F hfne ?_ fun j x hx => hpos j x
      (Finset.mem_filter.mp hx).1).trans ?_
    · intro x hx y hy
      simp only [Finset.mem_filter] at hx hy
      simp [LinearMap.mem_ker, map_sub, hx.2, hy.2]
    · have hnn : ∀ j, 0 ≤ ∑ y ∈ (S.filter fun x => ψ k x = ψ k x₁).image (ψ j), F j y := by
        intro j
        refine Finset.sum_nonneg fun y hy => ?_
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact (hpos j x (Finset.mem_filter.mp hx).1).le
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
      refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hnn j) _)
        (hpos k x₁ hx₁).le
      · have himg : (S.filter fun x => ψ k x = ψ k x₁).image (ψ k) = {ψ k x₁} := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_image.mpr
            ⟨x₁, by simp [hx₁], rfl⟩, fun y hy => ?_⟩
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          exact (Finset.mem_filter.mp hx).2
        rw [himg, Finset.sum_singleton, hk, Real.rpow_one]
      · refine Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg (hnn j) _)
          fun j _ => Real.rpow_le_rpow (hnn j) ?_ (hs j)
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.image_subset_image (Finset.filter_subset _ _)) fun y hy _ => ?_
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact (hpos j x hx).le
  calc ∑ x ∈ S, ∏ j, F j (ψ j x) ^ s j
      = ∑ c ∈ S.image (ψ k), ∑ x ∈ S with ψ k x = c, ∏ j, F j (ψ j x) ^ s j :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem _ hx) _).symm
    _ ≤ ∑ c ∈ S.image (ψ k), F k c * R := Finset.sum_le_sum hfib
    _ = A k ^ s k * R := by rw [← Finset.sum_mul, hk, Real.rpow_one]
    _ = ∏ j, A j ^ s j := Finset.mul_prod_erase Finset.univ (fun j => A j ^ s j)
        (Finset.mem_univ k)

/-- The dimension condition passes to the restriction of the datum to a subspace. -/
private theorem dimCond_restrict (ψ : ∀ j, V →ₗ[K] Vj j) {s : Fin m → ℝ} (U : Submodule K V)
    (h : DimCond ψ s) : DimCond (fun j => (ψ j).comp U.subtype) s := by
  intro W
  have h1 := h (W.map U.subtype)
  rw [← (Submodule.equivMapOfInjective _ U.injective_subtype W).finrank_eq] at h1
  refine h1.trans_eq (Finset.sum_congr rfl fun j _ => ?_)
  simp only
  rw [Submodule.map_comp]

/-- Rank–nullity for the restriction of a linear map to a finite-dimensional subspace. -/
private theorem finrank_map_add_finrank_inf_ker {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (A : Submodule K M)
    [FiniteDimensional K A] :
    finrank K (A.map f) + finrank K (A ⊓ LinearMap.ker f : Submodule K M) = finrank K A := by
  have h := LinearMap.lift_rank_map_add_rank_inf_ker f A
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at h
  simp only [Cardinal.lift_natCast] at h
  exact_mod_cast h

/-- The dimension condition passes to the induced datum on the quotient by a critical
subspace. -/
private theorem dimCond_quotient [FiniteDimensional K V] (ψ : ∀ j, V →ₗ[K] Vj j)
    {s : Fin m → ℝ} (W : Submodule K V) (h : DimCond ψ s)
    (hW : (finrank K W : ℝ) = ∑ j, s j * (finrank K (W.map (ψ j)) : ℝ)) :
    DimCond (fun j => W.mapQ (W.map (ψ j)) (ψ j) (Submodule.le_comap_map (ψ j) W)) s := by
  intro Q
  set U := Q.comap W.mkQ
  have hWU : W ≤ U := by
    intro x hx
    simp [U, (Submodule.Quotient.mk_eq_zero W).mpr hx]
  have hQ : U.map W.mkQ = Q := Submodule.map_comap_eq_of_surjective W.mkQ_surjective Q
  have e1 := finrank_map_add_finrank_inf_ker W.mkQ U
  rw [Submodule.ker_mkQ, inf_of_le_right hWU, hQ] at e1
  have e2 : ∀ j, finrank K (Q.map (W.mapQ (W.map (ψ j)) (ψ j)
      (Submodule.le_comap_map (ψ j) W))) + finrank K (W.map (ψ j)) =
      finrank K (U.map (ψ j)) := by
    intro j
    have := finrank_map_add_finrank_inf_ker (W.map (ψ j)).mkQ (U.map (ψ j))
    rw [Submodule.ker_mkQ, inf_of_le_right (Submodule.map_mono hWU)] at this
    rwa [← hQ, ← Submodule.map_comp, Submodule.mapQ_mkQ, Submodule.map_comp]
  have hU := h U
  have e1' : (finrank K Q : ℝ) = finrank K U - finrank K W := by
    rw [← e1]
    push_cast
    ring
  rw [e1', hW]
  calc (finrank K U : ℝ) - ∑ j, s j * (finrank K (W.map (ψ j)) : ℝ)
      ≤ ∑ j, s j * (finrank K (U.map (ψ j)) : ℝ) -
        ∑ j, s j * (finrank K (W.map (ψ j)) : ℝ) := by linarith
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← e2 j]
      push_cast
      ring

/-- An extreme point `s` of the polytope on a nonzero space has a critical subspace
`0 < W < V`, or some `sₖ = 1` with `ψₖ ≠ 0`: otherwise some `sᵢ` lies strictly between `0`
and `1`, and a perturbation `s ± ε v` supported on such coordinates stays in the polytope. -/
private theorem false_of_mem_extremePoints [FiniteDimensional K V] (ψ : ∀ j, V →ₗ[K] Vj j)
    {s : Fin m → ℝ} (hs : s ∈ (polytope ψ).extremePoints ℝ) (hV : 0 < finrank K V)
    (hcrit : ∀ W : Submodule K V, 0 < finrank K W → finrank K W < finrank K V →
      (finrank K W : ℝ) ≠ ∑ j, s j * (finrank K (W.map (ψ j)) : ℝ))
    (hone : ∀ k, s k = 1 → ψ k = 0) : False := by
  obtain ⟨hsP, hext⟩ := mem_extremePoints.mp hs
  set n := finrank K V with hn
  set r : Fin m → ℕ := fun j => finrank K ((⊤ : Submodule K V).map (ψ j)) with hr
  set slack : Submodule K V → ℝ := fun W =>
    ∑ j, s j * (finrank K (W.map (ψ j)) : ℝ) - finrank K W with hslack
  have hslack0 : ∀ W, 0 ≤ slack W := fun W => sub_nonneg.mpr (hsP.2 W)
  have hle : ∀ W : Submodule K V, finrank K W ≤ n := fun W => Submodule.finrank_le W
  have hlej : ∀ (W : Submodule K V) j, finrank K (W.map (ψ j)) ≤ n :=
    fun W j => (Submodule.finrank_map_le _ _).trans (hle W)
  have hzero : ∀ j, ¬ (0 < s j ∧ s j < 1) → s j * (r j : ℝ) = 0 := by
    intro j hj
    rcases (hsP.1 j).1.eq_or_lt with h | h
    · rw [← h, zero_mul]
    · have h1 : s j = 1 := le_antisymm (hsP.1 j).2 (not_lt.mp fun h' => hj ⟨h, h'⟩)
      simp [hr, hone j h1]
  -- a coordinate strictly between `0` and `1`
  obtain ⟨i, hi0, hi1⟩ : ∃ i, 0 < s i ∧ s i < 1 := by
    by_contra hcon
    have h := hsP.2 ⊤
    rw [Finset.sum_eq_zero fun j _ => hzero j fun hj => hcon ⟨j, hj⟩, finrank_top] at h
    have : (0 : ℝ) < n := by exact_mod_cast hV
    linarith
  -- a uniform lower bound for the positive slacks
  obtain ⟨δ, hδ, hδW⟩ : ∃ δ > 0, ∀ W, 0 < slack W → δ ≤ slack W := by
    have hfin : (Set.range slack).Finite := by
      refine (Set.finite_univ.image (fun p : (Fin m → Fin (n + 1)) × Fin (n + 1) =>
        ∑ j, s j * ((p.1 j : ℕ) : ℝ) - ((p.2 : ℕ) : ℝ))).subset ?_
      rintro _ ⟨W, rfl⟩
      exact ⟨(fun j => ⟨finrank K (W.map (ψ j)), Nat.lt_succ_of_le (hlej W j)⟩,
        ⟨finrank K W, Nat.lt_succ_of_le (hle W)⟩), trivial, rfl⟩
    by_cases hT : {x ∈ Set.range slack | 0 < x}.Nonempty
    · obtain ⟨δ, hδT, hδmin⟩ := Set.exists_min_image {x ∈ Set.range slack | 0 < x} id
        (hfin.subset fun x hx => hx.1) hT
      exact ⟨δ, hδT.2, fun W hW => hδmin (slack W) ⟨⟨W, rfl⟩, hW⟩⟩
    · exact ⟨1, one_pos, fun W hW => absurd ⟨slack W, ⟨W, rfl⟩, hW⟩ hT⟩
  -- a direction of perturbation
  obtain ⟨v, hv0, hvs, hvtop⟩ : ∃ v : Fin m → ℝ, v ≠ 0 ∧
      (∀ j, v j ≠ 0 → 0 < s j ∧ s j < 1) ∧ (slack ⊤ = 0 → ∑ j, v j * (r j : ℝ) = 0) := by
    by_cases hA : slack ⊤ ≠ 0 ∨ r i = 0
    · refine ⟨Pi.single i 1, fun h => by simpa using congr_fun h i, fun j hj => ?_,
        fun h0 => ?_⟩
      · by_cases hji : j = i
        · subst hji
          exact ⟨hi0, hi1⟩
        · simp [hji] at hj
      · rcases hA with hA | hA
        · exact absurd h0 hA
        · simp [Pi.single_apply, hA]
    · simp only [not_or, not_not] at hA
      obtain ⟨htop, hri⟩ := hA
      obtain ⟨k, hki, hk0, hk1⟩ : ∃ k, k ≠ i ∧ 0 < s k ∧ s k < 1 := by
        by_contra hcon
        have hsum : ∑ j, s j * (r j : ℝ) = s i * r i :=
          Finset.sum_eq_single i (fun j _ hji => hzero j fun hj => hcon ⟨j, hji, hj⟩)
            (by simp)
        have htop' : (n : ℝ) = s i * r i := by
          have : slack ⊤ = ∑ j, s j * (r j : ℝ) - n := by simp [hslack, hr, hn]
          linarith
        have hri' : (r i : ℝ) ≤ n := by exact_mod_cast hlej ⊤ i
        have hripos : (0 : ℝ) < r i := by exact_mod_cast Nat.pos_of_ne_zero hri
        nlinarith
      refine ⟨Pi.single i (r k : ℝ) - Pi.single k (r i : ℝ), fun h => ?_, fun j hj => ?_,
        fun _ => ?_⟩
      · have := congr_fun h k
        exact hri (by simpa [hki] using this)
      · by_cases hji : j = i
        · subst hji
          exact ⟨hi0, hi1⟩
        by_cases hjk : j = k
        · subst hjk
          exact ⟨hk0, hk1⟩
        simp [hji, hjk] at hj
      · simp [sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
        ring
  -- the size of the perturbation
  set M : ℝ := ∑ j, |v j| + 1 with hM
  have hMpos : 0 < M := by positivity
  set μ : ℝ := Finset.univ.inf' ⟨i, Finset.mem_univ i⟩ fun j =>
    if 0 < s j ∧ s j < 1 then min (s j) (1 - s j) else 1
  have hμ : 0 < μ := by
    refine (Finset.lt_inf'_iff _).mpr fun j _ => ?_
    split_ifs with h
    · exact lt_min h.1 (by linarith [h.2])
    · exact one_pos
  have hμj : ∀ j, 0 < s j ∧ s j < 1 → μ ≤ s j ∧ μ ≤ 1 - s j := by
    intro j hj
    have := Finset.inf'_le (fun j => if 0 < s j ∧ s j < 1 then min (s j) (1 - s j) else 1)
      (Finset.mem_univ j)
    rw [ite_eq_left hj] at this
    exact ⟨this.trans (min_le_left _ _), this.trans (min_le_right _ _)⟩
  set ν : ℝ := min μ (δ / (n + 1)) with hν
  have hνpos : 0 < ν := lt_min hμ (by positivity)
  set ε : ℝ := ν / (2 * M) with hε
  have hεpos : 0 < ε := by positivity
  have hεM : ε * M = ν / 2 := by
    rw [hε]
    field_simp
  have hmem : ∀ t : ℝ, |t| ≤ ε → s + t • v ∈ polytope ψ := by
    intro t ht
    refine ⟨fun j => ?_, fun W => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hvj : v j = 0
      · simpa [hvj] using hsP.1 j
      · obtain ⟨h0, h1⟩ := hμj j (hvs j hvj)
        have hvM : |v j| ≤ M := by
          have := Finset.single_le_sum (f := fun j => |v j|) (fun j _ => abs_nonneg (v j))
            (Finset.mem_univ j)
          linarith
        have htv : |t * v j| ≤ ν / 2 := by
          rw [abs_mul, ← hεM]
          exact mul_le_mul ht hvM (abs_nonneg _) hεpos.le
        have hνμ : ν ≤ μ := min_le_left _ _
        have := neg_abs_le (t * v j)
        have := le_abs_self (t * v j)
        constructor <;> linarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
      have hbound : |∑ j, t * v j * (finrank K (W.map (ψ j)) : ℝ)| < δ := by
        calc |∑ j, t * v j * (finrank K (W.map (ψ j)) : ℝ)|
            ≤ ∑ j, |t * v j * (finrank K (W.map (ψ j)) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j, |t| * |v j| * (n : ℝ) := Finset.sum_le_sum fun j _ => by
              rw [abs_mul, abs_mul, Nat.abs_cast]
              exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlej W j) (by positivity)
          _ = |t| * (n : ℝ) * ∑ j, |v j| := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by ring
          _ ≤ ε * (n : ℝ) * M := by
              gcongr
              linarith
          _ = ν / 2 * n := by rw [mul_right_comm, hεM]
          _ ≤ δ / (n + 1) / 2 * n := by
              gcongr
              exact min_le_right _ _
          _ < δ := by
              rw [div_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
              nlinarith
      by_cases hpos : 0 < slack W
      · have := hδW W hpos
        have := neg_abs_le (∑ j, t * v j * (finrank K (W.map (ψ j)) : ℝ))
        simp only [hslack] at this hpos ⊢
        linarith
      · have h0 : slack W = 0 := le_antisymm (not_lt.mp hpos) (hslack0 W)
        by_cases hW0 : finrank K W = 0
        · have hb : ∀ j, finrank K (W.map (ψ j)) = 0 := fun j => by
            rw [Submodule.finrank_eq_zero.mp hW0, Submodule.map_bot, finrank_bot]
          simp [hb, hW0]
        have hWn : finrank K W = n := by
          by_contra hne
          exact hcrit W (Nat.pos_of_ne_zero hW0) (lt_of_le_of_ne (hle W) hne)
            (by simp only [hslack] at h0; linarith)
        have hWtop : W = ⊤ := Submodule.eq_top_of_finrank_eq hWn
        subst hWtop
        have hv := hvtop h0
        have : ∑ j, t * v j * (r j : ℝ) = 0 := by
          simp_rw [mul_assoc, ← Finset.mul_sum, hv, mul_zero]
        simp only [hslack] at h0
        simp only [hr] at this
        linarith
  have h1 := hmem ε (by rw [abs_of_pos hεpos])
  have h2 := hmem (-ε) (by rw [abs_neg, abs_of_pos hεpos])
  have hseg : s ∈ openSegment ℝ (s + ε • v) (s + (-ε) • v) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring⟩
  have heq := (hext _ h1 _ h2 hseg).1
  apply hv0
  have : ε • v = 0 := by simpa using heq
  exact (smul_eq_zero.mp this).resolve_left hεpos.ne'

end Datum

/-- **The vector-space inequality.** The dimension condition gives the multilinear inequality,
by strong induction on the dimension. -/
private theorem funIneq_of_dimCond (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V], finrank K V = n →
    ∀ (Vj : Fin m → Type v) [∀ j, AddCommGroup (Vj j)] [∀ j, Module K (Vj j)]
      (ψ : ∀ j, V →ₗ[K] Vj j) (s : Fin m → ℝ), s ∈ polytope ψ → FunIneq ψ s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn Vj _ _ ψ
  have hext : (polytope ψ).extremePoints ℝ ⊆ {s | FunIneq ψ s} := by
    intro s hs
    have hsP : s ∈ polytope ψ := hs.1
    have hs0 : ∀ j, 0 ≤ s j := fun j => (hsP.1 j).1
    by_cases hV : finrank K V = 0
    · exact funIneq_of_finrank_eq_zero ψ s hV
    by_cases hcrit : ∃ W : Submodule K V, 0 < finrank K W ∧ finrank K W < finrank K V ∧
        (finrank K W : ℝ) = ∑ j, s j * (finrank K (W.map (ψ j)) : ℝ)
    · obtain ⟨W, hW0, hWn, hWc⟩ := hcrit
      apply funIneq_of_quotient ψ W hs0
      · exact ih (finrank K W) (hn ▸ hWn) W rfl Vj _ s ⟨hsP.1, dimCond_restrict ψ W hsP.2⟩
      · have hq : finrank K (V ⧸ W) < n := by
          have := Submodule.finrank_quotient_add_finrank W
          omega
        exact ih _ hq (V ⧸ W) rfl (fun j => Vj j ⧸ W.map (ψ j)) _ s
          ⟨hsP.1, dimCond_quotient ψ W hsP.2 hWc⟩
    by_cases hone : ∃ k, s k = 1 ∧ ψ k ≠ 0
    · obtain ⟨k, hk1, hk0⟩ := hone
      apply funIneq_of_fiber ψ k hk1 hs0
      have hlt : finrank K (LinearMap.ker (ψ k)) < n := by
        rw [← hn]
        apply Submodule.finrank_lt
        intro h
        exact hk0 (LinearMap.ker_eq_top.mp h)
      exact ih _ hlt (LinearMap.ker (ψ k)) rfl Vj _ s ⟨hsP.1, dimCond_restrict ψ _ hsP.2⟩
    exfalso
    push Not at hcrit hone
    exact false_of_mem_extremePoints ψ hs (Nat.pos_of_ne_zero hV) hcrit hone
  intro s hs
  have hKM := closure_convexHull_extremePoints (polytope_isCompact ψ) (polytope_convex ψ)
  have hsub : polytope ψ ⊆ {s | FunIneq ψ s} := by
    rw [← hKM]
    exact closure_minimal (convexHull_min hext (funIneq_convex ψ)) (funIneq_isClosed ψ)
  exact hsub hs

end Field

/-! ### From `ℤ^d` to `ℚ^d` -/

section Reduction

/-- The `ℚ`-linear extension of an additive map `ℤ^d → ℤ^k`, through its integer matrix. -/
private noncomputable def ratExt {d k : ℕ} (φ : (Fin d → ℤ) →+ (Fin k → ℤ)) :
    (Fin d → ℚ) →ₗ[ℚ] (Fin k → ℚ) :=
  Matrix.mulVecLin ((LinearMap.toMatrix' φ.toIntLinearMap).map (Int.cast : ℤ → ℚ))

/-- `ratExt φ` extends `φ`. -/
private theorem ratExt_apply_cast {d k : ℕ} (φ : (Fin d → ℤ) →+ (Fin k → ℤ)) (x : Fin d → ℤ) :
    ratExt φ (fun i => (x i : ℚ)) = fun l => ((φ x l : ℤ) : ℚ) := by
  funext l
  have h1 : (LinearMap.toMatrix' φ.toIntLinearMap).mulVec x = φ x := by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have h2 := RingHom.map_mulVec (Int.castRingHom ℚ) (LinearMap.toMatrix' φ.toIntLinearMap) x l
  rw [h1] at h2
  simp only [ratExt, Matrix.mulVecLin_apply]
  exact h2.symm

/-- The coordinatewise cast `ℤ^k → ℚ^k`, as a `ℤ`-linear map. -/
private def castVec (k : ℕ) : (Fin k → ℤ) →ₗ[ℤ] (Fin k → ℚ) :=
  LinearMap.compLeft (Algebra.linearMap ℤ ℚ) (Fin k)

private theorem castVec_apply (k : ℕ) (x : Fin k → ℤ) :
    castVec k x = fun i => (x i : ℚ) := by
  funext i
  simp [castVec]

private theorem castVec_injective (k : ℕ) : Function.Injective (castVec k) := by
  intro x y hxy
  funext i
  have := congrFun hxy i
  simpa [castVec_apply] using this

/-- The subgroup of integer vectors whose cast lies in `W`. -/
private def lattice {d : ℕ} (W : Submodule ℚ (Fin d → ℚ)) : AddSubgroup (Fin d → ℤ) :=
  W.toAddSubgroup.comap (castVec d).toAddMonoidHom

private theorem mem_lattice {d : ℕ} (W : Submodule ℚ (Fin d → ℚ)) (x : Fin d → ℤ) :
    x ∈ lattice W ↔ castVec d x ∈ W := Iff.rfl

/-- A subspace of `ℚ^d` has dimension at most the rank of its lattice of integer vectors. -/
private theorem finrank_le_finrank_lattice {d : ℕ} (W : Submodule ℚ (Fin d → ℚ)) :
    finrank ℚ W ≤ finrank ℤ (lattice W) := by
  let B := Module.finBasis ℚ W
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ)
    (Finset.univ : Finset (Fin (finrank ℚ W) × Fin d)) (fun p => (B p.1 : Fin d → ℚ) p.2)
  choose z hz using fun p : Fin (finrank ℚ W) × Fin d => hb p (Finset.mem_univ p)
  let Z : Fin (finrank ℚ W) → (Fin d → ℤ) := fun i l => z (i, l)
  have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have hZ : ∀ i, castVec d (Z i) = ((b : ℤ) : ℚ) • (B i : Fin d → ℚ) := by
    intro i
    funext l
    have := hz (i, l)
    simp only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul] at this
    simp [castVec_apply, Z, this]
  have hZmem : ∀ i, Z i ∈ (lattice W).toIntSubmodule := by
    intro i
    change castVec d (Z i) ∈ W
    rw [hZ i]
    exact W.smul_mem _ (B i).2
  have hindQ : LinearIndependent ℚ (fun i => ((b : ℤ) : ℚ) • (B i : Fin d → ℚ)) := by
    have h0 : LinearIndependent ℚ (fun i => (B i : Fin d → ℚ)) :=
      B.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    have := h0.units_smul (fun _ => Units.mk0 ((b : ℤ) : ℚ) hb0)
    convert this using 1
    funext i
    simp [Units.smul_def]
  have hindZ : LinearIndependent ℤ (fun i => castVec d (Z i)) := by
    rw [LinearIndependent.iff_fractionRing ℤ ℚ]
    simpa only [hZ] using hindQ
  have hZind : LinearIndependent ℤ Z := LinearIndependent.of_comp (castVec d) hindZ
  let Z' : Fin (finrank ℚ W) → (lattice W).toIntSubmodule := fun i => ⟨Z i, hZmem i⟩
  have hZ'ind : LinearIndependent ℤ Z' :=
    LinearIndependent.of_comp ((lattice W).toIntSubmodule.subtype) hZind
  have := hZ'ind.fintype_card_le_finrank
  exact (by simpa using this : finrank ℚ W ≤ finrank ℤ (lattice W).toIntSubmodule)

/-- The rank of the image of the lattice of `W` is at most the dimension of the image of `W`. -/
private theorem finrank_map_lattice_le {d k : ℕ} (φ : (Fin d → ℤ) →+ (Fin k → ℤ))
    (W : Submodule ℚ (Fin d → ℚ)) :
    finrank ℤ ((lattice W).map φ) ≤ finrank ℚ (W.map (ratExt φ)) := by
  let L := ((lattice W).map φ).toIntSubmodule
  change finrank ℤ L ≤ _
  let c := Module.finBasis ℤ L
  let v : Fin (finrank ℤ L) → (Fin k → ℚ) := fun i => castVec k (c i : Fin k → ℤ)
  have hvZ : LinearIndependent ℤ v :=
    (c.linearIndependent.map' L.subtype (Submodule.ker_subtype L)).map' (castVec k)
      (LinearMap.ker_eq_bot.mpr (castVec_injective k))
  have hvQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hvZ
  have hvmem : ∀ i, v i ∈ W.map (ratExt φ) := by
    intro i
    have hci : (c i : Fin k → ℤ) ∈ (lattice W).map φ := (c i).2
    obtain ⟨x, hx, hxe⟩ := AddSubgroup.mem_map.mp hci
    refine ⟨castVec d x, hx, ?_⟩
    simp only [v, castVec_apply, ← hxe]
    exact ratExt_apply_cast φ x
  let v' : Fin (finrank ℤ L) → W.map (ratExt φ) := fun i => ⟨v i, hvmem i⟩
  have hv'Q : LinearIndependent ℚ v' :=
    LinearIndependent.of_comp (W.map (ratExt φ)).subtype hvQ
  have := hv'Q.fintype_card_le_finrank
  simpa using this

/-- The rank condition on subgroups of `ℤ^d` gives the dimension condition on subspaces
of `ℚ^d` for the `ℚ`-linear extensions. -/
private theorem dimCond_ratExt {d m : ℕ} (dj : Fin m → ℕ)
    (φ : (j : Fin m) → (Fin d → ℤ) →+ (Fin (dj j) → ℤ)) (s : Fin m → ℝ)
    (hs : ∀ j, 0 ≤ s j)
    (h : ∀ H : AddSubgroup (Fin d → ℤ),
        (Module.finrank ℤ H : ℝ) ≤ ∑ j, s j * (Module.finrank ℤ (H.map (φ j)) : ℝ))
    (W : Submodule ℚ (Fin d → ℚ)) :
    (Module.finrank ℚ W : ℝ) ≤ ∑ j, s j * (Module.finrank ℚ (W.map (ratExt (φ j))) : ℝ) := by
  calc (finrank ℚ W : ℝ) ≤ finrank ℤ (lattice W) := by
        exact_mod_cast finrank_le_finrank_lattice W
    _ ≤ ∑ j, s j * (finrank ℤ ((lattice W).map (φ j)) : ℝ) := h _
    _ ≤ ∑ j, s j * (finrank ℚ (W.map (ratExt (φ j))) : ℝ) := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hs j)
        exact_mod_cast finrank_map_lattice_le (φ j) W

end Reduction

/-! ### The converse: lattice boxes -/

section Converse

/-- The box `[0, N)^r` of lattice points in `ℤ^r`. -/
private def box (r N : ℕ) : Finset (Fin r → ℤ) :=
  Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) N

private theorem card_box (r N : ℕ) : (box r N).card = N ^ r := by
  simp [box, Fintype.card_piFinset, Int.card_Ico]

private theorem box_nonempty (r N : ℕ) (hN : 1 ≤ N) : (box r N).Nonempty := by
  refine ⟨0, ?_⟩
  simp only [box, Fintype.mem_piFinset, Pi.zero_apply, Finset.mem_Ico, le_refl, true_and]
  intro _
  exact_mod_cast hN

/-- The image of the box `[0, N)^r` under a linear map `ℤ^r → ℤ^ρ` lies in a cube of side
`2 C N + 1`, for a constant `C` independent of `N`. -/
private theorem card_image_box_le_pi {r ρ : ℕ} (L : (Fin r → ℤ) →ₗ[ℤ] (Fin ρ → ℤ)) :
    ∃ C : ℕ, ∀ N : ℕ, ((box r N).image L).card ≤ (2 * C * N + 1) ^ ρ := by
  classical
  set c : Fin r → Fin ρ → ℤ := fun i => L fun j => if i = j then 1 else 0 with hc
  refine ⟨∑ i, ∑ l, (c i l).natAbs, fun N => ?_⟩
  set C := ∑ i, ∑ l, (c i l).natAbs with hC
  have hCint : (C : ℤ) = ∑ i, ∑ l, |c i l| := by
    simp [hC]
  have hsub : (box r N).image L ⊆
      Fintype.piFinset fun _ => Finset.Icc (-((C : ℤ) * N)) ((C : ℤ) * N) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [Fintype.mem_piFinset]
    intro l
    rw [Finset.mem_Icc, ← abs_le]
    have hxi : ∀ i, |x i| ≤ N := by
      intro i
      have := Fintype.mem_piFinset.mp hx i
      rw [Finset.mem_Ico] at this
      rw [abs_of_nonneg this.1]
      exact this.2.le
    have hLx : L x l = ∑ i, x i * c i l := by
      conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ L x]
      simp [hc, Finset.sum_apply]
    rw [hLx]
    calc |∑ i, x i * c i l| ≤ ∑ i, |x i * c i l| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |x i| * |c i l| := by simp only [abs_mul]
      _ ≤ ∑ i, (N : ℤ) * ∑ l', |c i l'| := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine mul_le_mul (hxi i) ?_ (abs_nonneg _) (by positivity)
          exact Finset.single_le_sum (f := fun l' => |c i l'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ l)
      _ = (C : ℤ) * N := by rw [← Finset.mul_sum, hCint, mul_comm]
  calc ((box r N).image L).card
      ≤ (Fintype.piFinset fun _ : Fin ρ =>
          Finset.Icc (-((C : ℤ) * N)) ((C : ℤ) * N)).card := Finset.card_le_card hsub
    _ = (2 * C * N + 1) ^ ρ := by
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Int.card_Icc]
        congr 1
        have : (C : ℤ) * N + 1 - -((C : ℤ) * N) = ((2 * C * N + 1 : ℕ) : ℤ) := by
          push_cast
          ring
        rw [this, Int.toNat_natCast]

/-- The image of the box `[0, N)^r` under a linear map `ψ : ℤ^r → ℤ^k` has at most
`(2 C N + 1) ^ ρ` points, where `ρ` is the rank of the range of `ψ` and `C` does not depend on
`N`. -/
private theorem card_image_box_le {r k : ℕ} (ψ : (Fin r → ℤ) →ₗ[ℤ] (Fin k → ℤ)) :
    ∃ C : ℕ, ∀ N : ℕ,
      ((box r N).image ψ).card ≤ (2 * C * N + 1) ^ finrank ℤ (LinearMap.range ψ) := by
  classical
  set c := Module.finBasis ℤ (LinearMap.range ψ)
  set L : (Fin r → ℤ) →ₗ[ℤ] (Fin (finrank ℤ (LinearMap.range ψ)) → ℤ) :=
    c.equivFun.toLinearMap ∘ₗ ψ.rangeRestrict with hL
  obtain ⟨C, hC⟩ := card_image_box_le_pi L
  refine ⟨C, fun N => ?_⟩
  have himage : (box r N).image ψ =
      ((box r N).image L).image (fun v => (c.equivFun.symm v : Fin k → ℤ)) := by
    rw [Finset.image_image]
    refine Finset.image_congr fun x _ => ?_
    simp only [Function.comp_apply, hL, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    rfl
  rw [himage]
  exact Finset.card_image_le.trans (hC N)

/-- Converse direction of the discrete HBL inequality (the box argument). -/
private theorem rank_le_of_card_le {d m : ℕ} (dj : Fin m → ℕ)
    (φ : (j : Fin m) → (Fin d → ℤ) →+ (Fin (dj j) → ℤ)) (s : Fin m → ℝ)
    (hs : ∀ j, s j ∈ Set.Icc (0 : ℝ) 1)
    (h : ∀ E : Finset (Fin d → ℤ), E.Nonempty →
        (E.card : ℝ) ≤ ∏ j, ((E.image (φ j)).card : ℝ) ^ s j)
    (H : AddSubgroup (Fin d → ℤ)) :
    (Module.finrank ℤ H : ℝ) ≤ ∑ j, s j * (Module.finrank ℤ (H.map (φ j)) : ℝ) := by
  classical
  set S := H.toIntSubmodule with hS
  set b := Module.finBasis ℤ S
  set r := Module.finrank ℤ S with hr
  set e : (Fin r → ℤ) →ₗ[ℤ] (Fin d → ℤ) := S.subtype ∘ₗ b.equivFun.symm.toLinearMap with he
  have he_inj : Function.Injective e := by
    intro a a' haa'
    have : b.equivFun.symm a = b.equivFun.symm a' := Subtype.ext haa'
    exact b.equivFun.symm.injective this
  have he_mem : ∀ a, e a ∈ H := fun a => (b.equivFun.symm a).2
  have he_surj : ∀ y ∈ H, ∃ a, e a = y := by
    intro y hy
    refine ⟨b.equivFun (⟨y, hy⟩ : S), ?_⟩
    simp [he]
  set ψ : ∀ j, (Fin r → ℤ) →ₗ[ℤ] (Fin (dj j) → ℤ) := fun j => (φ j).toIntLinearMap ∘ₗ e
    with hψ
  have hψ_apply : ∀ j a, ψ j a = φ j (e a) := fun _ _ => rfl
  have hrankj : ∀ j, Module.finrank ℤ (H.map (φ j)) =
      Module.finrank ℤ (LinearMap.range (ψ j)) := by
    intro j
    have hsub : (H.map (φ j)).toIntSubmodule = LinearMap.range (ψ j) := by
      ext y
      change y ∈ H.map (φ j) ↔ y ∈ LinearMap.range (ψ j)
      simp only [AddSubgroup.mem_map, LinearMap.mem_range, hψ_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨a, rfl⟩ := he_surj x hx
        exact ⟨a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨e a, he_mem a, rfl⟩
    change Module.finrank ℤ (H.map (φ j)).toIntSubmodule = _
    rw [hsub]
  have hrankH : Module.finrank ℤ H = r := rfl
  rw [hrankH]
  simp_rw [hrankj]
  set ρ : Fin m → ℕ := fun j => Module.finrank ℤ (LinearMap.range (ψ j)) with hρ
  choose C hC using fun j => card_image_box_le (ψ j)
  set σ : ℝ := ∑ j, s j * (ρ j : ℝ) with hσ
  set B : ℝ := ∏ j, ((2 * C j + 1 : ℕ) : ℝ) ^ (s j * (ρ j : ℝ)) with hB
  have hs0 : ∀ j, 0 ≤ s j := fun j => (hs j).1
  -- the counting inequality on the boxes
  have key : ∀ N : ℕ, 1 ≤ N → (N : ℝ) ^ (r : ℝ) ≤ B * (N : ℝ) ^ σ := by
    intro N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    set E := (box r N).image e with hE
    have hEne : E.Nonempty := (box_nonempty r N hN).image e
    have hEcard : E.card = N ^ r := by
      rw [hE, Finset.card_image_of_injective _ he_inj, card_box]
    have hEimage : ∀ j, E.image (φ j) = (box r N).image (ψ j) := by
      intro j
      rw [hE, Finset.image_image]
      rfl
    have h1 := h E hEne
    rw [hEcard] at h1
    calc (N : ℝ) ^ (r : ℝ) = ((N ^ r : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]
          push_cast
          rfl
      _ ≤ ∏ j, ((E.image (φ j)).card : ℝ) ^ s j := h1
      _ ≤ ∏ j, ((((2 * C j + 1 : ℕ) : ℝ) * N) ^ ρ j) ^ s j := by
          refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
          refine Real.rpow_le_rpow (by positivity) ?_ (hs0 j)
          rw [hEimage j]
          calc (((box r N).image (ψ j)).card : ℝ)
              ≤ ((2 * C j * N + 1) ^ ρ j : ℕ) := by exact_mod_cast hC j N
            _ ≤ (((2 * C j + 1 : ℕ) : ℝ) * N) ^ ρ j := by
                push_cast
                refine pow_le_pow_left₀ (by positivity) ?_ _
                have : (1 : ℝ) ≤ N := by exact_mod_cast hN
                nlinarith
      _ = ∏ j, (((2 * C j + 1 : ℕ) : ℝ) ^ (s j * (ρ j : ℝ)) *
            (N : ℝ) ^ (s j * (ρ j : ℝ))) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← Real.rpow_natCast_mul (by positivity), mul_comm (ρ j : ℝ) (s j),
            Real.mul_rpow (by positivity) hNpos.le]
      _ = B * (N : ℝ) ^ σ := by
          rw [Finset.prod_mul_distrib, hσ, Real.rpow_sum_of_pos hNpos]
  -- letting `N → ∞`
  by_contra hlt
  rw [not_le] at hlt
  set δ : ℝ := (r : ℝ) - σ with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hbound : ∀ N : ℕ, 1 ≤ N → (N : ℝ) ^ δ ≤ B := by
    intro N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 := key N hN
    have hsplit : (N : ℝ) ^ (r : ℝ) = (N : ℝ) ^ σ * (N : ℝ) ^ δ := by
      rw [← Real.rpow_add hNpos, hδ]
      ring_nf
    rw [hsplit, mul_comm B] at h1
    exact le_of_mul_le_mul_left h1 (Real.rpow_pos_of_pos hNpos σ)
  have htend : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ δ) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hδpos).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN1, hNB⟩ :=
    ((Filter.eventually_ge_atTop 1).and (htend.eventually_gt_atTop B)).exists
  exact absurd (hbound N hN1) (not_le.mpr hNB)

end Converse

/-- Two images of a finite set have the same cardinality when the maps agree up to an injection.
The decidability instances are implicit so that they unify with those of the goal. -/
private theorem card_image_image_eq {α β γ δ : Type*} {_ : DecidableEq β}
    {_ : DecidableEq γ} {_ : DecidableEq δ} (E : Finset α) {ι : α → β} {ψ : β → γ}
    {φ : α → δ} {ι' : δ → γ} (hι' : Function.Injective ι') (h : ∀ x, ψ (ι x) = ι' (φ x)) :
    ((E.image ι).image ψ).card = (E.image φ).card := by
  rw [Finset.image_image, show ψ ∘ ι = ι' ∘ φ from funext h, ← Finset.image_image,
    Finset.card_image_of_injective _ hι']

/-- **Discrete Hölder–Brascamp–Lieb inequality.** Let `φⱼ : ℤ^d → ℤ^{dⱼ}` (`j = 1, …, m`) be
group homomorphisms and `s ∈ [0, 1]^m`. Then `rank H ≤ ∑ⱼ sⱼ rank φⱼ(H)` for all subgroups
`H ≤ ℤ^d` if and only if `|E| ≤ ∏ⱼ |φⱼ(E)|^{sⱼ}` for all nonempty finite sets `E ⊆ ℤ^d`
(Christ, Demmel, Knight, Scanlon and Yelick, arXiv:1308.0068, Theorem 3.2). The rank of a
subgroup of `ℤ^k` is its rank as a free `ℤ`-module. -/
theorem rank_le_iff_card_le_prod {d m : ℕ} (dj : Fin m → ℕ)
    (φ : (j : Fin m) → (Fin d → ℤ) →+ (Fin (dj j) → ℤ)) (s : Fin m → ℝ)
    (hs : ∀ j, s j ∈ Set.Icc (0 : ℝ) 1) :
    (∀ H : AddSubgroup (Fin d → ℤ),
        (Module.finrank ℤ H : ℝ) ≤ ∑ j, s j * (Module.finrank ℤ (H.map (φ j)) : ℝ)) ↔
      ∀ E : Finset (Fin d → ℤ), E.Nonempty →
        (E.card : ℝ) ≤ ∏ j, ((E.image (φ j)).card : ℝ) ^ s j := by
  refine ⟨fun h E hE => ?_, fun h H => rank_le_of_card_le dj φ s hs h H⟩
  have hdim : DimCond (fun j => ratExt (φ j)) s :=
    dimCond_ratExt dj φ s (fun j => (hs j).1) h
  have hfun := funIneq_of_dimCond (K := ℚ) _ (Fin d → ℚ) rfl (fun j => Fin (dj j) → ℚ)
    (fun j => ratExt (φ j)) s ⟨hs, hdim⟩
  have h1 := hfun (E.image (castVec d)) (fun _ _ => 1) (hE.image _) fun _ _ _ => one_pos
  simp only [Real.one_rpow, Finset.prod_const_one, Finset.sum_const, nsmul_eq_mul,
    mul_one] at h1
  rw [Finset.card_image_of_injective _ (castVec_injective d)] at h1
  refine h1.trans_eq (Finset.prod_congr rfl fun j _ => ?_)
  have key : ∀ x, ratExt (φ j) (castVec d x) = castVec (dj j) (φ j x) := fun x => by
    simp only [castVec_apply]
    exact ratExt_apply_cast (φ j) x
  congr 2
  exact card_image_image_eq E (castVec_injective _) key

end MathlibExt.Combinatorics.DiscreteHolderBrascampLiebWanted
