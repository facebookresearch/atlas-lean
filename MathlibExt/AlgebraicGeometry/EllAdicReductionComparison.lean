/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EllAdicCohomology

@[expose] public noncomputable section

/-!
# Normalized reduction maps for integral pro-étale cohomology

The coefficient maps below are continuous additive maps pinned pointwise to
the actual reduction homomorphisms. The inverse limit is the subgroup of
compatible finite-level cohomology classes. Neither injectivity nor
surjectivity of the resulting cohomology map is assumed here.

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

local instance finiteTopology (m : ℕ) : TopologicalSpace (ZMod m) := ⊥
local instance finiteDiscrete (m : ℕ) : DiscreteTopology (ZMod m) := ⟨rfl⟩

/-- The continuous realizations of the canonical coefficient reductions.
These are characterized input maps, not arbitrary coefficient operators. -/
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

variable [ReductionMaps ell] (X : Scheme.{u}) (i : ℕ)

/-- The existing integral carrier, expressed by its defining coefficient sheaf.
This avoids opaque presentation differences in additive instance synthesis. -/
abbrev integralCohomology :=
  ((coefficientLift X).obj (coefficientSheaf X ℤ_[ell])).H i

/-- The displayed carrier is definitionally Mathlib's integral cohomology. -/
theorem integralCohomology_eq : integralCohomology ell X i =
    X.EllAdicCohomology ell i := rfl

/-- The actual finite-coefficient cohomology group on the same pro-étale site. -/
abbrev finiteCohomology (r : ℕ) :=
  ((coefficientLift X).obj
    (coefficientSheaf X (ZMod (ell ^ (r + 1))))).H i

/-- The transition induced by the actual coefficient quotient. -/
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

/-- Reduction compatibility is a precise equation between coefficient-induced
cohomology maps; it is sufficient to form the comparison cone. -/
def ReductionsCommute : Prop :=
  ∀ r x, transition ell X i r (reduction ell X i (r + 1) x) =
    reduction ell X i r x

/-- The canonical comparison, with all coordinates fixed by coefficient maps. -/
def comparison (h : ReductionsCommute ell X i) :
    integralCohomology ell X i →+ finiteLimit ell X i where
  toFun x := ⟨fun r => reduction ell X i r x, fun r => h r x⟩
  map_zero' := Subtype.ext (funext fun _r => map_zero _)
  map_add' x y := Subtype.ext (funext fun _r => map_add _ x y)


set_option backward.isDefEq.respectTransparency false in
/-- The coefficient quotient law induces compatibility on cohomology. -/
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
