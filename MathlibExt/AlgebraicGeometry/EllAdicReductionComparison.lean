/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EllAdicCohomology
public import Mathlib.Topology.Instances.ZMod

@[expose] public noncomputable section

/-!
# Normalized reduction maps for integral pro-étale cohomology

The reductions `ℤ_ℓ → ℤ/ℓ^(r+1)` and the quotient maps `ℤ/ℓ^(r+2) → ℤ/ℓ^(r+1)` are continuous
(for the discrete topology on `ℤ/ℓ^(r+1)`), so they induce maps of coefficient sheaves and of
cohomology. The induced reductions on cohomology are compatible with the transitions, giving a
map from `H^i(X, ℤ_ℓ)` to the inverse limit of the `H^i(X, ℤ/ℓ^(r+1))`, the subgroup of
compatible families. Neither injectivity nor surjectivity of this map is claimed here.

Reference: Bhatt–Scholze, *The pro-étale topology for schemes*, §6.8;
Stacks 03UT and 09BT. The completed constant-sheaf construction in
AxiomMath/Stacks, `ProEtale/ExtensionByZero/AdicSheaves.lean`, uses the same
quotient-tower pattern, at revision c496df0d9beea9deaeabcea8492605f9a0a2313b.
-/

namespace MathlibExt.AlgebraicGeometry.EllAdicReductionComparison

open _root_.CategoryTheory _root_.AlgebraicGeometry
open EllAdicCohomology

universe u

variable (ell : ℕ) [Fact ell.Prime]

/-- The reduction maps `ℤ_ℓ → ℤ/ℓ^(r+1)` and `ℤ/ℓ^(r+2) → ℤ/ℓ^(r+1)` as continuous additive maps,
determined by `red_eq` and `step_eq`. The instance is `canonicalReductionMaps`. -/
class ReductionMaps where
  /-- Reduction from integral coefficients. -/
  red : ∀ r : ℕ, ℤ_[ell] →ₜ+ ZMod (ell ^ (r + 1))
  /-- Transition between finite coefficient rings. -/
  step : ∀ r : ℕ, ZMod (ell ^ (r + 2)) →ₜ+ ZMod (ell ^ (r + 1))
  /-- Pointwise normalization of reduction. -/
  red_eq : ∀ r x, red r x = PadicInt.toZModPow (r + 1) x
  /-- Reduction and transition are compatible. -/
  comp : ∀ r x, step r (red (r + 1) x) = red r x
  /-- The transition is the canonical quotient of coefficient rings. -/
  step_eq : ∀ r x, step r x =
    ZMod.castHom (pow_dvd_pow ell (by omega : r + 1 ≤ r + 2))
      (ZMod (ell ^ (r + 1))) x

/-- Reduction `ℤ_ℓ → ℤ/ℓⁿ` is continuous for the discrete topology on `ℤ/ℓⁿ`: its kernel is the
open ball `ℓⁿ ℤ_ℓ`. -/
theorem continuous_toZModPow (n : ℕ) : Continuous (PadicInt.toZModPow (p := ell) n) := by
  have hker : IsOpen ((PadicInt.toZModPow (p := ell) n) ⁻¹' {0}) := by
    have h : (PadicInt.toZModPow (p := ell) n) ⁻¹' {0} =
        Metric.closedBall 0 ((ell : ℝ) ^ (-(n : ℤ))) := by
      ext x
      rw [Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_closedBall, dist_zero_right,
        ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
    rw [h]
    exact IsUltrametricDist.isOpen_closedBall _
      (zpow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : ell.Prime).ne_zero))
  refine continuous_of_continuousAt_zero (PadicInt.toZModPow (p := ell) n).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, nhds_discrete (ZMod (ell ^ n)), Filter.tendsto_pure]
  exact hker.mem_nhds (by simp)

/-- The canonical reduction maps: `PadicInt.toZModPow` and the quotient maps
`ℤ/ℓ^(r+2) → ℤ/ℓ^(r+1)`. -/
instance canonicalReductionMaps : ReductionMaps ell where
  red r :=
    { toAddMonoidHom := (PadicInt.toZModPow (r + 1)).toAddMonoidHom
      continuous_toFun := continuous_toZModPow ell (r + 1) }
  step r :=
    { toAddMonoidHom := (ZMod.castHom (pow_dvd_pow ell (by omega : r + 1 ≤ r + 2))
        (ZMod (ell ^ (r + 1)))).toAddMonoidHom
      continuous_toFun := continuous_of_discreteTopology }
  red_eq _ _ := rfl
  comp r x := PadicInt.cast_toZModPow (r + 1) (r + 2) (by omega) x
  step_eq _ _ := rfl

variable [ReductionMaps ell] (X : Scheme.{u}) (i : ℕ)

/-- Integral cohomology `H^i(X, ℤ_ℓ)`, written through its coefficient sheaf. -/
abbrev integralCohomology :=
  ((coefficientLift X).obj (coefficientSheaf X ℤ_[ell])).H i

omit [ReductionMaps ell] in
/-- `integralCohomology`, the cohomology $H^i(X, \mathbb{Z}_\ell)$ of the coefficient sheaf of
continuous $\mathbb{Z}_\ell$-valued functions on the pro-étale site of $X$, equals the $\ell$-adic
cohomology `Scheme.EllAdicCohomology` of $X$ in degree $i$. -/
theorem integralCohomology_eq : integralCohomology ell X i =
    X.EllAdicCohomology ell i := rfl

/-- Cohomology with coefficients `ℤ/ℓ^(r+1)` on the pro-étale site. -/
abbrev finiteCohomology (r : ℕ) :=
  ((coefficientLift X).obj
    (coefficientSheaf X (ZMod (ell ^ (r + 1))))).H i

/-- The transition map induced by the quotient `ℤ/ℓ^(r+2) → ℤ/ℓ^(r+1)`. -/
def transition (r : ℕ) : finiteCohomology ell X i (r + 1) →+
    finiteCohomology ell X i r :=
  Sheaf.H.map ((coefficientLift X).map
    (coefficientMap X (ReductionMaps.step (ell := ell) r))) i

/-- Reduction of an integral cohomology class. -/
def reduction (r : ℕ) : integralCohomology ell X i →+
    finiteCohomology ell X i r :=
  Sheaf.H.map ((coefficientLift X).map
    (coefficientMap X (ReductionMaps.red (ell := ell) r))) i

/-- The inverse limit of finite-coefficient cohomology as compatible families. -/
def finiteLimit : AddSubgroup (∀ r : ℕ, finiteCohomology ell X i r) where
  carrier := {a | ∀ r, transition ell X i r (a (r + 1)) = a r}
  zero_mem' r := map_zero _
  add_mem' ha hb r := by simp [ha r, hb r]
  neg_mem' ha r := by simp [ha r]

/-- The reductions on cohomology are compatible with the transitions. -/
def ReductionsCommute : Prop :=
  ∀ r x, transition ell X i r (reduction ell X i (r + 1) x) =
    reduction ell X i r x

/-- The map from integral cohomology to the inverse limit of finite-level cohomology. -/
def comparison (h : ReductionsCommute ell X i) :
    integralCohomology ell X i →+ finiteLimit ell X i where
  toFun x := ⟨fun r => reduction ell X i r x, fun r => h r x⟩
  map_zero' := Subtype.ext (funext fun _r => map_zero _)
  map_add' x y := Subtype.ext (funext fun _r => map_add _ x y)


set_option backward.isDefEq.respectTransparency false in
/-- Reductions are compatible with transitions, since they are on coefficients. -/
theorem reductions_commute : ReductionsCommute ell X i := by
  intro r x
  have hg : globalCoefficientMap (ReductionMaps.red (ell := ell) (r + 1)) ≫
      globalCoefficientMap (ReductionMaps.step (ell := ell) r) =
      globalCoefficientMap (ReductionMaps.red (ell := ell) r) := by
    ext U s
    change C(U.unop, ℤ_[ell]) at s
    change (ReductionMaps.step (ell := ell) r).toContinuousMap.comp
        ((ReductionMaps.red (ell := ell) (r + 1)).toContinuousMap.comp s) =
      (ReductionMaps.red (ell := ell) r).toContinuousMap.comp s
    apply ContinuousMap.ext
    intro y
    exact ReductionMaps.comp r (s y)
  have hc : coefficientMap X (ReductionMaps.red (ell := ell) (r + 1)) ≫
      coefficientMap X (ReductionMaps.step (ell := ell) r) =
      coefficientMap X (ReductionMaps.red (ell := ell) r) := by
    change (coefficientPushforward X).map _ ≫
        (coefficientPushforward X).map _ = (coefficientPushforward X).map _
    rw [← Functor.map_comp, hg]
  have hl : (coefficientLift X).map
        (coefficientMap X (ReductionMaps.red (ell := ell) (r + 1))) ≫
      (coefficientLift X).map
        (coefficientMap X (ReductionMaps.step (ell := ell) r)) =
      (coefficientLift X).map
        (coefficientMap X (ReductionMaps.red (ell := ell) r)) := by
    rw [← Functor.map_comp, hc]
  exact (Sheaf.H.map_comp_apply _ _ x).symm.trans
    (congrArg (fun f => Sheaf.H.map f i x) hl)

end MathlibExt.AlgebraicGeometry.EllAdicReductionComparison
