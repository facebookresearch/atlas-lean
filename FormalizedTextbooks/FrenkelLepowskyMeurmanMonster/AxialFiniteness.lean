/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The quantitative isolation and compactness argument underlying Conway's
finiteness proof, Invent. Math. 79 (1985), §13, printed page 527.
The source's concrete spectrum and orbit-span hypotheses must be established
separately before applying these general analytic lemmas to the Griess algebra.
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

section QuantitativeIsolation
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The quadratic remainder of a symmetric bilinear multiplication at a
scaled idempotent is exactly the difference of its linearized equations. -/
theorem scaled_idempotent_difference
    (B : V →L[ℝ] V →L[ℝ] V) (hcomm : ∀ x y, B x y = B y x)
    (k : ℝ) (x y : V) (hx : B x x = k • x) (hy : B y y = k • y) :
    k • (y - x) - (2 : ℝ) • B x (y - x) = B (y - x) (y - x) := by
  simp only [map_sub, sub_apply, smul_sub, hcomm y x, hx, hy]
  module

/-- A lower bound on the linearized equation makes a scaled idempotent isolated.
The continuous bilinear operator norm supplies the exact quadratic remainder bound. -/
theorem scaled_idempotent_isolated
    (B : V →L[ℝ] V →L[ℝ] V) (hcomm : ∀ x y, B x y = B y x)
    (k : ℝ) (x y : V) (hx : B x x = k • x) (hy : B y y = k • y)
    (c : ℝ) (_hc : 0 < c)
    (hgap : ∀ v, c * ‖v‖ ≤ ‖k • v - (2 : ℝ) • B x v‖)
    (hclose : ‖y - x‖ < c / (‖B‖ + 1)) : y = x := by
  have hlinear := hgap (y - x)
  rw [scaled_idempotent_difference B hcomm k x y hx hy] at hlinear
  have hquad := B.le_opNorm₂ (y - x) (y - x)
  have hden : 0 < ‖B‖ + 1 := by positivity
  have hsmall : (‖B‖ + 1) * ‖y - x‖ < c :=
    by simpa only [mul_comm] using (lt_div_iff₀ hden).mp hclose
  by_contra hne
  have hn : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hstrict : ‖B‖ * ‖y - x‖ < c := by nlinarith [norm_nonneg B]
  nlinarith

/-- A totally bounded set of scaled idempotents with a uniform linearized gap is finite.
Finiteness follows from the analytic hypotheses, rather than being assumed. -/
theorem totallyBounded_scaled_idempotents_finite
    (B : V →L[ℝ] V →L[ℝ] V) (hcomm : ∀ x y, B x y = B y x)
    (k : ℝ) (S : Set V) (htotal : TotallyBounded S)
    (hidem : ∀ x ∈ S, B x x = k • x)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ x ∈ S, ∀ v, c * ‖v‖ ≤ ‖k • v - (2 : ℝ) • B x v‖) : S.Finite := by
  have hr : 0 < c / (‖B‖ + 1) := by positivity
  obtain ⟨T, hTS, hT, hcover⟩ := Metric.finite_approx_of_totallyBounded htotal _ hr
  apply hT.subset
  intro y hy
  obtain ⟨x, hxT, hdist⟩ := Set.mem_iUnion₂.mp (hcover hy)
  have hxS := hTS hxT
  have he : y = x := scaled_idempotent_isolated B hcomm k x y (hidem x hxS)
    (hidem y hy) c hc (hgap x hxS) (by simpa only [Metric.mem_ball, dist_eq_norm] using hdist)
  exact he ▸ hxT

/-- Compactness supplies total boundedness in the isolated-idempotent criterion. -/
theorem compact_scaled_idempotents_finite
    (B : V →L[ℝ] V →L[ℝ] V) (hcomm : ∀ x y, B x y = B y x)
    (k : ℝ) (S : Set V) (hcompact : IsCompact S)
    (hidem : ∀ x ∈ S, B x x = k • x)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ x ∈ S, ∀ v, c * ‖v‖ ≤ ‖k • v - (2 : ℝ) • B x v‖) : S.Finite :=
  totallyBounded_scaled_idempotents_finite B hcomm k S hcompact.totallyBounded hidem c hc hgap

/-- Convert Mathlib's bound for the inverse into the positive lower gap used by
Conway's isolation criterion. -/
theorem continuousLinearEquiv_positive_gap (e : V ≃L[ℝ] V) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, c * ‖v‖ ≤ ‖e v‖ := by
  obtain ⟨C, hC, hbound⟩ := e.symm.toContinuousLinearMap.bound
  refine ⟨C⁻¹, inv_pos.mpr hC, fun v => ?_⟩
  have h := hbound (e v)
  change ‖e.symm (e v)‖ ≤ C * ‖e v‖ at h
  rw [e.symm_apply_apply] at h
  simpa only [inv_mul_eq_div] using
    (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using h)

end QuantitativeIsolation
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
section AutomorphismOrbit
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual orbit of an axis under a subgroup of real linear equivalences. -/
def algebraAxisOrbit (A : Subgroup (V ≃ₗ[ℝ] V)) (x : V) : Set V :=
  Set.range (fun g : A => g.val x)

/-- A finite spanning orbit determines every linear group element by a finite
permutation. This is the last algebraic step in Conway's finiteness argument. -/
theorem linear_group_finite_of_spanning_orbit
    (A : Subgroup (V ≃ₗ[ℝ] V)) (x : V)
    (hfinite : (algebraAxisOrbit A x).Finite)
    (hspan : Submodule.span ℝ (algebraAxisOrbit A x) = ⊤) : Finite A := by
  classical
  let S := algebraAxisOrbit A x
  let : Finite S := hfinite.to_subtype
  have hpres (g : A) (y : S) : g.val y.val ∈ S := by
    obtain ⟨h, hh⟩ := y.property
    change h.val x = y.val at hh
    refine ⟨g * h, ?_⟩
    change g.val (h.val x) = g.val y.val
    rw [hh]
  let images : A → (S → S) := fun g y => ⟨g.val y.val, hpres g y⟩
  apply Finite.of_injective images
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hmem : v ∈ Submodule.span ℝ S := by rw [hspan]; trivial
  induction hmem using Submodule.span_induction with
  | mem y hy =>
    exact congrArg Subtype.val (congrFun he ⟨y, hy⟩)
  | zero => simp
  | add u v hu hv heu hev => simp only [map_add, heu, hev]
  | smul r y hy hey => simp only [map_smul, hey]

/-- Conway's analytic finiteness criterion: a norm-preserving algebra group
with a compact spanning orbit of a spectrally isolated scaled idempotent is finite.
The criterion derives finite orbit and finite group from concrete analytic inputs. -/
theorem algebra_axis_orbit_finite_of_totallyBounded_isolated
    (A : Subgroup (V ≃ₗ[ℝ] V))
    (B : V →L[ℝ] V →L[ℝ] V) (hcomm : ∀ u v, B u v = B v u)
    (hprod : ∀ g : A, ∀ u v, g.val (B u v) = B (g.val u) (g.val v))
    (hnorm : ∀ g : A, ∀ v, ‖g.val v‖ = ‖v‖)
    (k : ℝ) (x : V) (haxis : B x x = k • x)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ v, c * ‖v‖ ≤ ‖k • v - (2 : ℝ) • B x v‖)
    (htotal : TotallyBounded (algebraAxisOrbit A x)) : (algebraAxisOrbit A x).Finite := by
  have hidem : ∀ y ∈ algebraAxisOrbit A x, B y y = k • y := by
    intro y hy
    obtain ⟨g, rfl⟩ := hy
    change B (g.val x) (g.val x) = k • g.val x
    rw [← hprod, haxis, map_smul]
  have hgapOrbit : ∀ y ∈ algebraAxisOrbit A x, ∀ v,
      c * ‖v‖ ≤ ‖k • v - (2 : ℝ) • B y v‖ := by
    intro y hy v
    obtain ⟨g, rfl⟩ := hy
    let w := g.val.symm v
    have hw : g.val w = v := g.val.apply_symm_apply v
    have hn : ‖w‖ = ‖v‖ := by
      have h := hnorm g w
      rw [hw] at h
      exact h.symm
    have he : g.val (k • w - (2 : ℝ) • B x w) =
        k • v - (2 : ℝ) • B (g.val x) v := by
      rw [map_sub, map_smul, map_smul, hprod, hw]
    calc
      c * ‖v‖ = c * ‖w‖ := by rw [hn]
      _ ≤ ‖k • w - (2 : ℝ) • B x w‖ := hgap w
      _ = ‖g.val (k • w - (2 : ℝ) • B x w)‖ := (hnorm g _).symm
      _ = ‖k • v - (2 : ℝ) • B (g.val x) v‖ := by rw [he]
  exact totallyBounded_scaled_idempotents_finite B hcomm k _ htotal hidem c hc hgapOrbit

/-- A finite isolated axis orbit that spans determines the whole group. -/
theorem algebra_group_finite_of_totallyBounded_isolated_axis
    (A : Subgroup (V ≃ₗ[ℝ] V))
    (B : V →L[ℝ] V →L[ℝ] V) (hcomm : ∀ u v, B u v = B v u)
    (hprod : ∀ g : A, ∀ u v, g.val (B u v) = B (g.val u) (g.val v))
    (hnorm : ∀ g : A, ∀ v, ‖g.val v‖ = ‖v‖)
    (k : ℝ) (x : V) (haxis : B x x = k • x)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ v, c * ‖v‖ ≤ ‖k • v - (2 : ℝ) • B x v‖)
    (htotal : TotallyBounded (algebraAxisOrbit A x))
    (hspan : Submodule.span ℝ (algebraAxisOrbit A x) = ⊤) : Finite A :=
  linear_group_finite_of_spanning_orbit A x
    (algebra_axis_orbit_finite_of_totallyBounded_isolated A B hcomm hprod hnorm k x
      haxis c hc hgap htotal) hspan

/-- Compact-orbit form of Conway's spectral isolation criterion. -/
theorem algebra_group_finite_of_isolated_axis
    (A : Subgroup (V ≃ₗ[ℝ] V))
    (B : V →L[ℝ] V →L[ℝ] V) (hcomm : ∀ u v, B u v = B v u)
    (hprod : ∀ g : A, ∀ u v, g.val (B u v) = B (g.val u) (g.val v))
    (hnorm : ∀ g : A, ∀ v, ‖g.val v‖ = ‖v‖)
    (k : ℝ) (x : V) (haxis : B x x = k • x)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ v, c * ‖v‖ ≤ ‖k • v - (2 : ℝ) • B x v‖)
    (hcompact : IsCompact (algebraAxisOrbit A x))
    (hspan : Submodule.span ℝ (algebraAxisOrbit A x) = ⊤) : Finite A :=
  algebra_group_finite_of_totallyBounded_isolated_axis A B hcomm hprod hnorm k x haxis c hc
    hgap hcompact.totallyBounded hspan

/-- In a proper normed space, norm preservation automatically bounds the axis orbit
inside a compact ball. No compactness hypothesis on the group or orbit is needed. -/
theorem normPreserving_axis_orbit_totallyBounded [ProperSpace V]
    (A : Subgroup (V ≃ₗ[ℝ] V)) (x : V)
    (hnorm : ∀ g : A, ∀ v, ‖g.val v‖ = ‖v‖) : TotallyBounded (algebraAxisOrbit A x) := by
  apply (isCompact_closedBall (0 : V) ‖x‖).totallyBounded.subset
  intro y hy
  obtain ⟨g, rfl⟩ := hy
  change dist (g.val x) 0 ≤ ‖x‖
  rw [dist_zero_right, hnorm]

/-- The bounded-orbit form of Conway's finiteness criterion. -/
theorem algebra_group_finite_of_proper_isolated_axis [ProperSpace V]
    (A : Subgroup (V ≃ₗ[ℝ] V))
    (B : V →L[ℝ] V →L[ℝ] V) (hcomm : ∀ u v, B u v = B v u)
    (hprod : ∀ g : A, ∀ u v, g.val (B u v) = B (g.val u) (g.val v))
    (hnorm : ∀ g : A, ∀ v, ‖g.val v‖ = ‖v‖)
    (k : ℝ) (x : V) (haxis : B x x = k • x)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ v, c * ‖v‖ ≤ ‖k • v - (2 : ℝ) • B x v‖)
    (hspan : Submodule.span ℝ (algebraAxisOrbit A x) = ⊤) : Finite A :=
  algebra_group_finite_of_totallyBounded_isolated_axis A B hcomm hprod hnorm k x haxis c hc
    hgap (normPreserving_axis_orbit_totallyBounded A x hnorm) hspan

/-- The spectral criterion can equivalently be supplied as an actual inverse
for the linearized equation. No norm estimate on its inverse is assumed. -/
theorem algebra_group_finite_of_invertible_axis_linearization
    (A : Subgroup (V ≃ₗ[ℝ] V))
    (B : V →L[ℝ] V →L[ℝ] V) (hcomm : ∀ u v, B u v = B v u)
    (hprod : ∀ g : A, ∀ u v, g.val (B u v) = B (g.val u) (g.val v))
    (hnorm : ∀ g : A, ∀ v, ‖g.val v‖ = ‖v‖)
    (k : ℝ) (x : V) (haxis : B x x = k • x)
    (e : V ≃L[ℝ] V) (he : ∀ v, e v = k • v - (2 : ℝ) • B x v)
    (hcompact : IsCompact (algebraAxisOrbit A x))
    (hspan : Submodule.span ℝ (algebraAxisOrbit A x) = ⊤) : Finite A := by
  obtain ⟨c, hc, hgap⟩ := continuousLinearEquiv_positive_gap e
  apply algebra_group_finite_of_isolated_axis A B hcomm hprod hnorm k x haxis c hc _
    hcompact hspan
  intro v
  simpa only [he v] using hgap v

/-- An inverse for the linearized equation and a spanning orbit establish
finiteness in a proper space, with no compact-orbit assumption. -/
theorem algebra_group_finite_of_proper_invertible_axis [ProperSpace V]
    (A : Subgroup (V ≃ₗ[ℝ] V))
    (B : V →L[ℝ] V →L[ℝ] V) (hcomm : ∀ u v, B u v = B v u)
    (hprod : ∀ g : A, ∀ u v, g.val (B u v) = B (g.val u) (g.val v))
    (hnorm : ∀ g : A, ∀ v, ‖g.val v‖ = ‖v‖)
    (k : ℝ) (x : V) (haxis : B x x = k • x)
    (e : V ≃L[ℝ] V) (he : ∀ v, e v = k • v - (2 : ℝ) • B x v)
    (hspan : Submodule.span ℝ (algebraAxisOrbit A x) = ⊤) : Finite A := by
  obtain ⟨c, hc, hgap⟩ := continuousLinearEquiv_positive_gap e
  apply algebra_group_finite_of_proper_isolated_axis A B hcomm hprod hnorm k x haxis c hc _ hspan
  intro v
  simpa only [he v] using hgap v

/-- Any finite invariant set spanning the vector space determines the linear group. -/
theorem linear_group_finite_of_invariant_spanning_set
    (A : Subgroup (V ≃ₗ[ℝ] V)) (S : Set V) (hfinite : S.Finite)
    (hpres : ∀ g : A, ∀ y ∈ S, g.val y ∈ S)
    (hspan : Submodule.span ℝ S = ⊤) : Finite A := by
  classical
  let : Finite S := hfinite.to_subtype
  let images : A → (S → S) := fun g y => ⟨g.val y.val, hpres g y.val y.property⟩
  apply Finite.of_injective images
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hmem : v ∈ Submodule.span ℝ S := by rw [hspan]; trivial
  induction hmem using Submodule.span_induction with
  | mem y hy => exact congrArg Subtype.val (congrFun he ⟨y, hy⟩)
  | zero => simp
  | add u v hu hv heu hev => simp only [map_add, heu, hev]
  | smul r y hy hey => simp only [map_smul, hey]

/-- A finite family of isolated axes suffices: their individual orbits are
finite by the analytic estimate, and their invariant union spans the space.
No transitivity between the different axes is required. -/
theorem algebra_group_finite_of_proper_axis_family [ProperSpace V]
    {ι : Type*} [Finite ι]
    (A : Subgroup (V ≃ₗ[ℝ] V))
    (B : V →L[ℝ] V →L[ℝ] V) (hcomm : ∀ u v, B u v = B v u)
    (hprod : ∀ g : A, ∀ u v, g.val (B u v) = B (g.val u) (g.val v))
    (hnorm : ∀ g : A, ∀ v, ‖g.val v‖ = ‖v‖)
    (k : ℝ) (x : ι → V) (haxis : ∀ i, B (x i) (x i) = k • x i)
    (e : ι → (V ≃L[ℝ] V)) (he : ∀ i v, e i v = k • v - (2 : ℝ) • B (x i) v)
    (hspan : Submodule.span ℝ (⋃ i, algebraAxisOrbit A (x i)) = ⊤) : Finite A := by
  classical
  have hfinite (i : ι) : (algebraAxisOrbit A (x i)).Finite := by
    obtain ⟨c, hc, hgap⟩ := continuousLinearEquiv_positive_gap (e i)
    apply algebra_axis_orbit_finite_of_totallyBounded_isolated A B hcomm hprod hnorm k (x i)
      (haxis i) c hc _ (normPreserving_axis_orbit_totallyBounded A (x i) hnorm)
    intro v
    simpa only [he i v] using hgap v
  apply linear_group_finite_of_invariant_spanning_set A (⋃ i, algebraAxisOrbit A (x i))
    (Set.finite_iUnion hfinite) _ hspan
  intro g y hy
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
  obtain ⟨h, hh⟩ := hi
  apply Set.mem_iUnion.mpr
  refine ⟨i, g * h, ?_⟩
  change h.val (x i) = y at hh
  change g.val (h.val (x i)) = g.val y
  rw [hh]

end AutomorphismOrbit
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
