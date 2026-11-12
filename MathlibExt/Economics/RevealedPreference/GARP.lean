/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Algebra.Ring.Real

@[expose] public section

/-!
# Revealed preference: demand data and GARP

A record of demand observations `(pⁱ, xⁱ)` (prices and chosen bundles), the revealed-preference
relations `R⁰`, `P⁰` and `R`, the Generalized Axiom of Revealed Preference (GARP), and
rationalization by a utility function. The main result is the necessity direction of Afriat's
theorem: data rationalized by a locally nonsatiated utility function satisfy GARP.

Bundles range over all of `G → ℝ`, as in Varian's definition of rationalization; no sign
condition on prices or bundles is assumed, and observations need not be distinct.

## Main definitions

* `DemandData`: observed prices and bundles indexed by `ι`, over goods `G`.
* `DemandData.DirectlyRevealedPreferred`, `DemandData.StrictlyDirectlyRevealedPreferred`,
  `DemandData.RevealedPreferred`: Varian's `R⁰`, `P⁰` and `R`, restricted to observed
  bundles.
* `DemandData.GARP`, `DemandData.Rationalizes`, `LocallyNonsatiated`.

## Main results

* `DemandData.garp_of_rationalizes`: Afriat's theorem, (1) ⇒ (2).

## References

* H. R. Varian, "The Nonparametric Approach to Demand Analysis", Econometrica 50 (1982),
  945-973: definitions pp. 946-947; proof of (1) ⇒ (2) in Appendix I.
* S. N. Afriat, "The Construction of Utility Functions from Expenditure Data", International
  Economic Review 8 (1967), 67-77.
-/

namespace MathlibExt.Economics.RevealedPreference

/-- A record of demand observations `(pⁱ, xⁱ)` indexed by `ι`, over goods indexed by `G`
(Varian 1982, p. 945: "observations on these prices and quantities, `(pⁱ, xⁱ)`"). -/
structure DemandData (ι G : Type*) where
  /-- `price i` is the price vector `pⁱ` faced at observation `i`. -/
  price : ι → G → ℝ
  /-- `bundle i` is the bundle `xⁱ` chosen at observation `i`. -/
  bundle : ι → G → ℝ

namespace DemandData

/-- `xⁱ R⁰ xʲ`: `xⁱ` is directly revealed preferred to `xʲ`, i.e. `pⁱxⁱ ≥ pⁱxʲ`
(Varian 1982, p. 947, Definition (1)). -/
def DirectlyRevealedPreferred {ι G : Type*} [Fintype G] (D : DemandData ι G) (i j : ι) :
    Prop :=
  D.price i ⬝ᵥ D.bundle j ≤ D.price i ⬝ᵥ D.bundle i

/-- `xⁱ P⁰ xʲ`: `xⁱ` is strictly directly revealed preferred to `xʲ`, i.e. `pⁱxⁱ > pⁱxʲ`
(Varian 1982, p. 947, Definition (2)). -/
def StrictlyDirectlyRevealedPreferred {ι G : Type*} [Fintype G] (D : DemandData ι G)
    (i j : ι) : Prop :=
  D.price i ⬝ᵥ D.bundle j < D.price i ⬝ᵥ D.bundle i

/-- `xⁱ R xʲ`: `xⁱ` is revealed preferred to `xʲ`, the transitive closure of `R⁰`
(Varian 1982, p. 947, Definition (3)). Since `R⁰` is reflexive, so is `R`. -/
def RevealedPreferred {ι G : Type*} [Fintype G] (D : DemandData ι G) : ι → ι → Prop :=
  Relation.TransGen D.DirectlyRevealedPreferred

/-- The Generalized Axiom of Revealed Preference: `xⁱ R xʲ` implies not `xʲ P⁰ xⁱ`
(Varian 1982, p. 947, Definition (4); equivalently `pʲxʲ ≤ pʲxⁱ`, Appendix I). -/
def GARP {ι G : Type*} [Fintype G] (D : DemandData ι G) : Prop :=
  ∀ i j, D.RevealedPreferred i j → ¬ D.StrictlyDirectlyRevealedPreferred j i

/-- A utility function `u` rationalizes the data if `u xⁱ ≥ u x` for every `x` with
`pⁱxⁱ ≥ pⁱx` (Varian 1982, p. 946, Definition). -/
def Rationalizes {ι G : Type*} [Fintype G] (D : DemandData ι G) (u : (G → ℝ) → ℝ) : Prop :=
  ∀ i (y : G → ℝ), D.price i ⬝ᵥ y ≤ D.price i ⬝ᵥ D.bundle i → u y ≤ u (D.bundle i)

end DemandData

/-- Local nonsatiation: every bundle has arbitrarily close bundles of strictly higher utility
(the "nonsatiated" hypothesis of Afriat's theorem, used as local nonsatiation in Varian 1982,
Appendix I, proof of (1) ⇒ (2)). Distance is the sup metric on `G → ℝ`. -/
def LocallyNonsatiated {G : Type*} [Fintype G] (u : (G → ℝ) → ℝ) : Prop :=
  ∀ (y : G → ℝ) (ε : ℝ), 0 < ε → ∃ z, dist z y < ε ∧ u y < u z

/-- Afriat's theorem, (1) ⇒ (2): data rationalized by a locally nonsatiated utility function
satisfy GARP. -/
theorem DemandData.garp_of_rationalizes {ι G : Type*} [Fintype G] (D : DemandData ι G)
    {u : (G → ℝ) → ℝ} (hu : LocallyNonsatiated u) (hD : D.Rationalizes u) : D.GARP := by
  have hR0 : ∀ a b, D.DirectlyRevealedPreferred a b → u (D.bundle b) ≤ u (D.bundle a) :=
    fun a b h => hD a _ h
  have hR : ∀ a b, D.RevealedPreferred a b → u (D.bundle b) ≤ u (D.bundle a) := by
    intro a b h
    induction h with
    | single h => exact hR0 _ _ h
    | tail h1 h2 ih => exact le_trans (hR0 _ _ h2) ih
  have hStrict : ∀ a (y : G → ℝ),
      D.price a ⬝ᵥ y < D.price a ⬝ᵥ D.bundle a → u y < u (D.bundle a) := by
    intro a y hlt
    by_contra hcon
    push Not at hcon
    have hcont : Continuous (fun z : G → ℝ => D.price a ⬝ᵥ z) := by
      unfold dotProduct
      exact continuous_finsetSum Finset.univ fun g _ =>
        Continuous.mul continuous_const (continuous_apply g)
    have hcat : ContinuousAt (fun z : G → ℝ => D.price a ⬝ᵥ z) y :=
      hcont.continuousAt
    rw [Metric.continuousAt_iff] at hcat
    set gap := D.price a ⬝ᵥ D.bundle a - D.price a ⬝ᵥ y with hgap
    have hgap_pos : 0 < gap := sub_pos.mpr hlt
    obtain ⟨δ, hδpos, hδ⟩ := hcat gap hgap_pos
    obtain ⟨z, hz_dist, hz_util⟩ := hu y δ hδpos
    have hz_budget : D.price a ⬝ᵥ z ≤ D.price a ⬝ᵥ D.bundle a := by
      have hdist := hδ hz_dist
      rw [Real.dist_eq] at hdist
      have habs : D.price a ⬝ᵥ z - D.price a ⬝ᵥ y < gap := (abs_lt.mp hdist).2
      simp [hgap] at habs ⊢
      linarith
    have hle := hD a z hz_budget
    linarith
  intro i j hRij hPji
  have h1 : u (D.bundle j) ≤ u (D.bundle i) := hR i j hRij
  have h2 : u (D.bundle i) < u (D.bundle j) := hStrict j _ hPji
  linarith

end MathlibExt.Economics.RevealedPreference
