/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Dynamics.SystemsBiology
public import Mathlib.Analysis.Calculus.FDeriv.Basic
import MathlibExt.Analysis.Convex.LinearProgrammingBasic

/-!
# The flux balance value function: piecewise linearity and shadow prices

Flux balance analysis (FBA) is the linear program `max cᵀv` subject to `S v = b`, `l ≤ v ≤ u`
(`fbaValue S l u c b`, from `Domains.Biology.Dynamics.SystemsBiology`). Its dual minimizes
`b ⬝ᵥ y + u ⬝ᵥ α - l ⬝ᵥ β` over `α, β ≥ 0` with `Sᵀ y + α - β = c` (`fbaDualFeasible`).

The dual feasible set does not depend on `b`. Writing `y = y⁺ - y⁻`, it is a polyhedron in
standard form `{z ≥ 0 | L z = c}`, and a linear objective that attains its minimum on such a
polyhedron attains it at a basic point: one where no nonzero direction in the kernel of `L`
vanishes off the support of `z`. A basic point is determined by its support, so there are
finitely many. Hence the optimal value is, at every feasible `b`, the minimum of finitely
many affine functions `b ↦ y ⬝ᵥ b + κ`, one for each basic dual point.
Basic points are `MathlibExt.Analysis.Convex.LPBasic.IsBasicPt`.

Near an interior feasible `b` only the pieces active at `b` matter; if the optimal dual price
`y` is unique, all active pieces have slope `y`, so the value function is affine near `b` and
its derivative there is `b' ↦ y ⬝ᵥ b'` (the shadow prices of Orth, Thiele & Palsson).

## Main results

* `exists_finset_optimal_fbaDual`: a finite set of dual feasible pairs `(y, u ⬝ᵥ α - l ⬝ᵥ β)`
  containing an optimal dual solution for every feasible right-hand side.
* `exists_finset_isLeast_fbaValue`: on the feasible right-hand sides the optimal value is the
  minimum of finitely many affine functions of `b`, so it is piecewise linear.
* `hasFDerivAt_fbaValue_of_unique`: at an interior feasible `b` with a unique optimal dual
  price vector `y`, the optimal value is differentiable with derivative `b' ↦ y ⬝ᵥ b'`.

Off the feasible right-hand sides `fbaValue` is the junk value `sSup ∅ = 0`; every statement
here assumes feasibility (or an interior feasible point). Concavity and the identification of
the supergradients with the optimal dual prices are `fbaValue_concave` and
`exists_optimal_dual_iff_supergradient`.

## Not covered

The converse of the derivative statement (differentiability forces a unique optimal price), the
superdifferential at a boundary point of the feasible set, and an explicit description of the
pieces (the finite family is obtained from basic dual points, not listed).

## References

* J. D. Orth, I. Thiele, B. Ø. Palsson, "What is flux balance analysis?", Nat. Biotechnol. 28
  (2010) 245–248.
* R. T. Rockafellar, *Convex Analysis*, Princeton (1970), Thm 19.3 (polyhedral convex
  functions) and Thm 25.1 (differentiability and unique subgradients).
* A. Schrijver, *Theory of Linear and Integer Programming*, Wiley (1986), §8.5 (minimal faces
  and vertices) and §10.4 (sensitivity analysis).
-/

@[expose] public section

namespace MathlibExt.Biology.Dynamics.SystemsBiology

open Matrix
open MathlibExt.Analysis.Convex.LPBasic

/-! ### Minima of finitely many affine functions -/

section Affine

variable {m : ℕ}

/-- A function that, on a set `U`, is the minimum of finitely many affine functions
`b ↦ p.1 ⬝ᵥ b + p.2` is differentiable at an interior point `b` of `U` where every active piece
has slope `y`, with derivative `b' ↦ y ⬝ᵥ b'`. -/
private theorem hasFDerivAt_of_isLeast_affine {F : (Fin m → ℝ) → ℝ} {U : Set (Fin m → ℝ)}
    {b : Fin m → ℝ} (hb : b ∈ interior U) {T : Finset ((Fin m → ℝ) × ℝ)}
    (hT : ∀ b' ∈ U, IsLeast ((fun p : (Fin m → ℝ) × ℝ => p.1 ⬝ᵥ b' + p.2) '' (T : Set _))
      (F b'))
    {y : Fin m → ℝ} (hact : ∀ p ∈ T, p.1 ⬝ᵥ b + p.2 = F b → p.1 = y) :
    HasFDerivAt F
      (∑ i, y i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i) b := by
  set Λ := ∑ i, y i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i
  have hΛ : ∀ v, Λ v = y ⬝ᵥ v := fun v => by
    simp [Λ, dotProduct]
  have hU : U ∈ nhds b := mem_interior_iff_mem_nhds.1 hb
  obtain ⟨⟨q, hqT, hq⟩, hlow⟩ := hT b (interior_subset hb)
  simp only at hq
  -- inactive pieces stay strictly above the active piece `q` near `b`
  have hev : ∀ᶠ b' in nhds b, ∀ p ∈ T, p.1 ⬝ᵥ b + p.2 ≠ F b →
      q.1 ⬝ᵥ b' + q.2 < p.1 ⬝ᵥ b' + p.2 := by
    rw [Filter.eventually_all_finset]
    intro p hpT
    by_cases hp : p.1 ⬝ᵥ b + p.2 = F b
    · exact Filter.Eventually.of_forall fun _ h => absurd hp h
    · have hgt : q.1 ⬝ᵥ b + q.2 < p.1 ⬝ᵥ b + p.2 :=
        lt_of_le_of_ne (hq ▸ hlow ⟨p, hpT, rfl⟩) (hq ▸ Ne.symm hp)
      have hc : Continuous fun b' : Fin m → ℝ => (p.1 ⬝ᵥ b' + p.2) - (q.1 ⬝ᵥ b' + q.2) := by
        fun_prop
      have := hc.continuousAt.eventually (lt_mem_nhds (a := 0) (by linarith))
      exact this.mono fun b' hb' _ => by linarith
  have heq : F =ᶠ[nhds b] fun b' => F b + Λ (b' - b) := by
    filter_upwards [hev, hU] with b' hb' hb'U
    obtain ⟨⟨p, hpT, hp⟩, hlow'⟩ := hT b' hb'U
    simp only at hp
    have hpact : p.1 ⬝ᵥ b + p.2 = F b := by
      by_contra hne
      have h1 := hb' p hpT hne
      have h2 := hlow' ⟨q, hqT, rfl⟩
      simp only at h2
      linarith
    have hy := hact p hpT hpact
    rw [hΛ, ← hp, ← hpact, hy, dotProduct_sub]
    ring
  have hd : HasFDerivAt (fun b' => F b + Λ (b' - b)) Λ b := by
    have := ((Λ.hasFDerivAt (x := b)).const_add (F b)).sub_const (Λ b)
    simpa [map_sub, add_sub_assoc] using this
  exact hd.congr_of_eventuallyEq heq

end Affine

/-! ### Flux balance analysis -/

section FluxBalance

variable {m n : ℕ}

/-- Coordinates of the standard-form dual: `y = y⁺ - y⁻`, `α`, `β`, all nonnegative. -/
private abbrev DualIdx (m n : ℕ) : Type := (Fin m ⊕ Fin m) ⊕ (Fin n ⊕ Fin n)

/-- The price vector `y⁺ - y⁻` of a standard-form dual point. -/
private noncomputable def dualY : (DualIdx m n → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  LinearMap.funLeft ℝ ℝ (fun i => Sum.inl (Sum.inl i)) -
    LinearMap.funLeft ℝ ℝ (fun i => Sum.inl (Sum.inr i))

/-- The upper-bound multiplier `α` of a standard-form dual point. -/
private noncomputable def dualA : (DualIdx m n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.funLeft ℝ ℝ (fun j => Sum.inr (Sum.inl j))

/-- The lower-bound multiplier `β` of a standard-form dual point. -/
private noncomputable def dualB : (DualIdx m n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.funLeft ℝ ℝ (fun j => Sum.inr (Sum.inr j))

/-- The dual constraint map `z ↦ Sᵀ y + α - β`. -/
private noncomputable def dualL (S : Matrix (Fin m) (Fin n) ℝ) :
    (DualIdx m n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  Sᵀ.mulVecLin ∘ₗ dualY + dualA - dualB

/-- The dual objective as a linear functional of the standard-form point. -/
private noncomputable def dualObj (l u : Fin n → ℝ) (b : Fin m → ℝ) :
    (DualIdx m n → ℝ) →ₗ[ℝ] ℝ where
  toFun z := fbaDualValue l u b (dualY z) (dualA z) (dualB z)
  map_add' z w := by
    simp only [fbaDualValue, map_add, dotProduct_add]
    ring
  map_smul' a z := by
    simp only [fbaDualValue, map_smul, dotProduct_smul, smul_eq_mul, RingHom.id_apply]
    ring

private theorem dualL_apply (S : Matrix (Fin m) (Fin n) ℝ) (z : DualIdx m n → ℝ) :
    dualL S z = Sᵀ *ᵥ dualY z + dualA z - dualB z := rfl

/-- A nonnegative standard-form point with `L z = c` is dual feasible. -/
private theorem fbaDualFeasible_of_dualL {S : Matrix (Fin m) (Fin n) ℝ} {c : Fin n → ℝ}
    {z : DualIdx m n → ℝ} (hz : 0 ≤ z) (hL : dualL S z = c) :
    fbaDualFeasible S c (dualY z) (dualA z) (dualB z) :=
  ⟨fun _ => hz _, fun _ => hz _, hL⟩

/-- **Finitely many dual solutions suffice.** There is a finite set `T` of pairs
`(y, u ⬝ᵥ α - l ⬝ᵥ β)` with `(y, α, β)` dual feasible, such that for every feasible `b` some
pair in `T` is optimal: `y ⬝ᵥ b + κ = fbaValue S l u c b`. -/
theorem exists_finset_optimal_fbaDual (S : Matrix (Fin m) (Fin n) ℝ) (l u c : Fin n → ℝ) :
    ∃ T : Finset ((Fin m → ℝ) × ℝ),
      (∀ p ∈ T, ∃ α β, fbaDualFeasible S c p.1 α β ∧ p.2 = u ⬝ᵥ α - l ⬝ᵥ β) ∧
      ∀ b : Fin m → ℝ, (fbaFeasible S l u b).Nonempty →
        ∃ p ∈ T, p.1 ⬝ᵥ b + p.2 = fbaValue S l u c b := by
  classical
  have hP := finite_basic (dualL S) c
  refine ⟨hP.toFinset.image fun z => (dualY z, u ⬝ᵥ dualA z - l ⬝ᵥ dualB z), ?_, ?_⟩
  · intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨hz0, hLz, -⟩ := hP.mem_toFinset.1 hz
    exact ⟨dualA z, dualB z, fbaDualFeasible_of_dualL hz0 hLz, rfl⟩
  · intro b hb
    obtain ⟨y₀, α₀, β₀, ⟨hα₀, hβ₀, hc₀⟩, hV₀⟩ := exists_fbaDualValue_eq (c := c) hb
    obtain ⟨v, hv, hV, -⟩ := exists_fbaValue_eq (c := c) hb
    set z₀ : DualIdx m n → ℝ := Sum.elim (Sum.elim (fun i => max (y₀ i) 0)
      (fun i => max (-y₀ i) 0)) (Sum.elim α₀ β₀) with hz₀
    have hY : dualY z₀ = y₀ := by
      funext i
      simp [dualY, hz₀]
    have hA : dualA z₀ = α₀ := by funext j; simp [dualA, hz₀, LinearMap.funLeft_apply]
    have hB : dualB z₀ = β₀ := by funext j; simp [dualB, hz₀, LinearMap.funLeft_apply]
    have hz₀0 : 0 ≤ z₀ := by
      rintro ((i | i) | (j | j)) <;>
        simp only [hz₀, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply] <;>
        first | exact le_max_right _ _ | exact hα₀ j | exact hβ₀ j
    have hLz₀ : dualL S z₀ = c := by rw [dualL_apply, hY, hA, hB, hc₀]
    have hφz₀ : dualObj l u b z₀ = fbaValue S l u c b := by
      change fbaDualValue l u b (dualY z₀) (dualA z₀) (dualB z₀) = _
      rw [hY, hA, hB, hV₀]
    obtain ⟨z, hz0, hLz, hφz, hbas⟩ := exists_basic_optimal (dualL S) (dualObj l u b) c hz₀0
      hLz₀ fun z' hz' hLz' => by
        rw [hφz₀, hV]
        exact dotProduct_le_fbaDualValue hv (fbaDualFeasible_of_dualL hz' hLz')
    refine ⟨_, Finset.mem_image_of_mem _ (hP.mem_toFinset.2 ⟨hz0, hLz, hbas⟩), ?_⟩
    rw [← hφz₀, ← hφz]
    change _ = fbaDualValue l u b (dualY z) (dualA z) (dualB z)
    simp only [fbaDualValue, dotProduct_comm (dualY z) b]
    ring

/-- The finite family of `exists_finset_optimal_fbaDual` attains the minimum at every
feasible `b`. -/
private theorem isLeast_of_optimal_fbaDual {S : Matrix (Fin m) (Fin n) ℝ} {l u c : Fin n → ℝ}
    {T : Finset ((Fin m → ℝ) × ℝ)}
    (hT₁ : ∀ p ∈ T, ∃ α β, fbaDualFeasible S c p.1 α β ∧ p.2 = u ⬝ᵥ α - l ⬝ᵥ β)
    (hT₂ : ∀ b : Fin m → ℝ, (fbaFeasible S l u b).Nonempty →
      ∃ p ∈ T, p.1 ⬝ᵥ b + p.2 = fbaValue S l u c b)
    {b : Fin m → ℝ} (hb : (fbaFeasible S l u b).Nonempty) :
    IsLeast ((fun p : (Fin m → ℝ) × ℝ => p.1 ⬝ᵥ b + p.2) '' (T : Set _))
      (fbaValue S l u c b) := by
  obtain ⟨p, hpT, hp⟩ := hT₂ b hb
  refine ⟨⟨p, hpT, hp⟩, ?_⟩
  rintro _ ⟨q, hqT, rfl⟩
  obtain ⟨α, β, hd, hq⟩ := hT₁ q hqT
  obtain ⟨v, hv, hV, -⟩ := exists_fbaValue_eq (c := c) hb
  have := dotProduct_le_fbaDualValue hv hd
  simp only [fbaDualValue] at this
  change fbaValue S l u c b ≤ q.1 ⬝ᵥ b + q.2
  rw [hV, hq, dotProduct_comm q.1 b]
  linarith

/-- **The FBA value is piecewise linear.** There are finitely many affine functions
`b ↦ y ⬝ᵥ b + κ` whose minimum is the optimal value at every feasible right-hand side `b`.

Source: Rockafellar (1970), Thm 19.3; Orth, Thiele & Palsson (2010). -/
theorem exists_finset_isLeast_fbaValue (S : Matrix (Fin m) (Fin n) ℝ)
    (l u c : Fin n → ℝ) :
    ∃ T : Finset ((Fin m → ℝ) × ℝ), ∀ b : Fin m → ℝ, (fbaFeasible S l u b).Nonempty →
      IsLeast ((fun p : (Fin m → ℝ) × ℝ => p.1 ⬝ᵥ b + p.2) '' (T : Set _))
        (fbaValue S l u c b) := by
  obtain ⟨T, hT₁, hT₂⟩ := exists_finset_optimal_fbaDual S l u c
  exact ⟨T, fun b hb => isLeast_of_optimal_fbaDual hT₁ hT₂ hb⟩

/-- **Shadow prices are derivatives when unique.** If `b` is an interior point of the set of
feasible right-hand sides and `y` is the only metabolite price vector of an optimal dual
solution, then the optimal value is differentiable at `b` with derivative `b' ↦ y ⬝ᵥ b'`.

Source: Rockafellar (1970), Thm 25.1; Orth, Thiele & Palsson (2010). -/
theorem hasFDerivAt_fbaValue_of_unique {S : Matrix (Fin m) (Fin n) ℝ}
    {l u c : Fin n → ℝ} {b : Fin m → ℝ}
    (hb : b ∈ interior {b' : Fin m → ℝ | (fbaFeasible S l u b').Nonempty}) {y : Fin m → ℝ}
    (huniq : ∀ y' : Fin m → ℝ, (∃ α β, fbaDualFeasible S c y' α β ∧
        ∀ y'' α'' β'', fbaDualFeasible S c y'' α'' β'' →
          fbaDualValue l u b y' α β ≤ fbaDualValue l u b y'' α'' β'') ↔ y' = y) :
    HasFDerivAt (fbaValue S l u c)
      (∑ i, y i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i) b := by
  obtain ⟨T, hT₁, hT₂⟩ := exists_finset_optimal_fbaDual S l u c
  have hbF : (fbaFeasible S l u b).Nonempty := (interior_subset hb :)
  refine hasFDerivAt_of_isLeast_affine hb (fun b' hb' => isLeast_of_optimal_fbaDual hT₁ hT₂ hb')
    fun p hpT hp => (huniq p.1).1 ?_
  obtain ⟨α, β, hd, hκ⟩ := hT₁ p hpT
  obtain ⟨v, hv, hV, -⟩ := exists_fbaValue_eq (c := c) hbF
  refine ⟨α, β, hd, fun y'' α'' β'' hd'' => ?_⟩
  have h1 : fbaDualValue l u b p.1 α β = fbaValue S l u c b := by
    rw [← hp, hκ, fbaDualValue, dotProduct_comm b p.1]
    ring
  rw [h1, hV]
  exact dotProduct_le_fbaDualValue hv hd''

end FluxBalance

end MathlibExt.Biology.Dynamics.SystemsBiology
