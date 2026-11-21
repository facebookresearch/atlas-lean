/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality
public import MathlibExt.AlgebraicGeometry.EllAdicReductionComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Continuous adic compact-support realization by the closed-boundary kernel

The compact-support coefficient object is the actual kernel of
F -> i_* i^* F for a closed boundary i. The unit and both functors are
the actual small pro-étale ones. Taking the kernel in the functor category
supplies functorial coefficient maps and all their identity/composition
laws. For a quasi-compact open complement this is j_! j^* F, by the
completed open-closed exactness theorem of Stacks 09AH.

The finite reductions and inverse-limit map are prescribed coefficient
maps on this kernel. Their compatibility is proved below. The native
continuous compact-support/finite-level realization is a separate goal.

References: Stacks Project, Tags 09AH, 03UT and 09BT; Bhatt--Scholze,
The pro-étale topology for schemes, §6.8.
-/

namespace MathlibExt.AlgebraicGeometry.ContinuousAdicCompactSupports

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality
open MathlibExt.AlgebraicGeometry.EllAdicCohomology
open MathlibExt.AlgebraicGeometry.EllAdicReductionComparison

universe u

/-- The actual abelian sheaf category on the small pro-étale site. -/
abbrev AdicAbelianSheaf (X : Scheme.{u}) := Sheaf (ProEt.topology X) Ab.{u + 1}

abbrev abelianPushforward {Y X : Scheme.{u}} (f : Y ⟶ X) :
    AdicAbelianSheaf Y ⥤ AdicAbelianSheaf X :=
  (baseChange f).sheafPushforwardContinuous Ab.{u + 1}
    (ProEt.topology X) (ProEt.topology Y)

abbrev abelianPullback {Y X : Scheme.{u}} (f : Y ⟶ X) :
    AdicAbelianSheaf X ⥤ AdicAbelianSheaf Y :=
  Functor.sheafPullbackConstruction.sheafPullback (baseChange f) Ab.{u + 1}
    (ProEt.topology X) (ProEt.topology Y)

def abelianAdjunction {Y X : Scheme.{u}} (f : Y ⟶ X) :
    abelianPullback f ⊣ abelianPushforward f :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

/-- The actual kernel functor of the actual closed-immersion unit. -/
def boundaryKernelFunctor {Z X : Scheme.{u}} (i : Z ⟶ X) :
    AdicAbelianSheaf X ⥤ AdicAbelianSheaf X :=
  kernel (abelianAdjunction i).unit

/-- A proper compactification and its genuine closed boundary. -/
structure ClosedCompactification {k : Type u} [Field k] (X : Over (Spec (.of k))) where
  /-- The actual proper ambient scheme over k. -/
  ambient : Over (Spec (.of k))
  /-- The actual open map from X to the proper ambient scheme. -/
  openMap : X ⟶ ambient
  /-- The actual boundary scheme. -/
  boundary : Scheme.{u}
  /-- The actual closed boundary immersion. -/
  closedMap : boundary ⟶ ambient.left
  proper : IsProper ambient.hom
  openImmersion : IsOpenImmersion openMap.left
  closedImmersion : IsClosedImmersion closedMap
  /-- The displayed open is precisely the complement of the boundary. -/
  complement : Set.range openMap.left.base = (Set.range closedMap.base)ᶜ

attribute [instance] ClosedCompactification.proper ClosedCompactification.openImmersion
  ClosedCompactification.closedImmersion

/-- Actual lifted continuous coefficients, using the native adic carrier. -/
abbrev actualCoefficient {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (c : ClosedCompactification X) (A : Type) [TopologicalSpace A] [AddCommGroup A]
    [IsTopologicalAddGroup A] : AdicAbelianSheaf c.ambient.left :=
  (coefficientLift c.ambient.left).obj (coefficientSheaf c.ambient.left A)

/-- The actual compact-support coefficient sheaf. -/
abbrev compactSupportCoefficient {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (c : ClosedCompactification X) (A : Type) [TopologicalSpace A] [AddCommGroup A]
    [IsTopologicalAddGroup A] : AdicAbelianSheaf c.ambient.left :=
  (boundaryKernelFunctor c.closedMap).obj (actualCoefficient c A)

/-- Actual compact-support sheaf cohomology of the displayed kernel. -/
abbrev compactSupportCohomology {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (c : ClosedCompactification X) (A : Type) [TopologicalSpace A] [AddCommGroup A]
    [IsTopologicalAddGroup A] (n : ℕ) :=
  (compactSupportCoefficient c A).H n

/-- The actual coefficient map, followed by the functorial boundary kernel. -/
def compactCoefficientMap {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (c : ClosedCompactification X) {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    [AddCommGroup A] [AddCommGroup B] [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
    (f : A →ₜ+ B) : compactSupportCoefficient c A ⟶ compactSupportCoefficient c B :=
  (boundaryKernelFunctor c.closedMap).map
    ((coefficientLift c.ambient.left).map (coefficientMap c.ambient.left f))

variable (ell : ℕ) [Fact ell.Prime] [ReductionMaps ell]

local instance finiteTopology (m : ℕ) : TopologicalSpace (ZMod m) := ⊥
local instance finiteDiscrete (m : ℕ) : DiscreteTopology (ZMod m) := ⟨rfl⟩

variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
  (c : ClosedCompactification X) (n : ℕ)

/-- The actual integral compact-support cohomology carrier. -/
abbrev integralCompactSupport := compactSupportCohomology c ℤ_[ell] n

/-- Actual finite-level compact-support cohomology on the same site. -/
abbrev finiteCompactSupport (r : ℕ) :=
  compactSupportCohomology c (ZMod (ell ^ (r + 1))) n

/-- The transition is induced by the prescribed coefficient quotient. -/
def compactTransition (r : ℕ) : finiteCompactSupport ell c n (r + 1) →+
    finiteCompactSupport ell c n r :=
  Sheaf.H.map (compactCoefficientMap c (ReductionMaps.step (ell := ell) r)) n

/-- Reduction of an integral compact-support class is a genuine sheaf map. -/
def compactReduction (r : ℕ) : integralCompactSupport ell c n →+
    finiteCompactSupport ell c n r :=
  Sheaf.H.map (compactCoefficientMap c (ReductionMaps.red (ell := ell) r)) n

/-- The finite-level coefficient comparison is compatible on the actual kernels. -/
theorem compactReductionsCommute (r : ℕ) (x : integralCompactSupport ell c n) :
    compactTransition ell c n r (compactReduction ell c n (r + 1) x) =
      compactReduction ell c n r x := by
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
  have hc : coefficientMap c.ambient.left (ReductionMaps.red (ell := ell) (r + 1)) ≫
      coefficientMap c.ambient.left (ReductionMaps.step (ell := ell) r) =
        coefficientMap c.ambient.left (ReductionMaps.red (ell := ell) r) := by
    change (coefficientPushforward c.ambient.left).map _ ≫
      (coefficientPushforward c.ambient.left).map _ =
        (coefficientPushforward c.ambient.left).map _
    rw [← CategoryTheory.Functor.map_comp, hg]
  have hl : (coefficientLift c.ambient.left).map
      (coefficientMap c.ambient.left (ReductionMaps.red (ell := ell) (r + 1))) ≫
        (coefficientLift c.ambient.left).map
          (coefficientMap c.ambient.left (ReductionMaps.step (ell := ell) r)) =
      (coefficientLift c.ambient.left).map
        (coefficientMap c.ambient.left (ReductionMaps.red (ell := ell) r)) := by
    rw [← CategoryTheory.Functor.map_comp, hc]
  have hk : compactCoefficientMap c (ReductionMaps.red (ell := ell) (r + 1)) ≫
      compactCoefficientMap c (ReductionMaps.step (ell := ell) r) =
        compactCoefficientMap c (ReductionMaps.red (ell := ell) r) := by
    change (boundaryKernelFunctor c.closedMap).map _ ≫
      (boundaryKernelFunctor c.closedMap).map _ =
        (boundaryKernelFunctor c.closedMap).map _
    rw [← CategoryTheory.Functor.map_comp, hl]
  exact (Sheaf.H.map_comp_apply _ _ x).symm.trans
    (congrArg (fun f ↦ Sheaf.H.map f n x) hk)

/-- The actual inverse limit is the subgroup of compatible finite-level classes. -/
def compactFiniteLimit : AddSubgroup (∀ r : ℕ, finiteCompactSupport ell c n r) where
  carrier := {a | ∀ r, compactTransition ell c n r (a (r + 1)) = a r}
  zero_mem' r := map_zero _
  add_mem' ha hb r := by simp [ha r, hb r]
  neg_mem' ha r := by simp [ha r]

/-- Every coordinate of this comparison is fixed by the actual reduction map. -/
def compactSupportLimitComparison : integralCompactSupport ell c n →+
    compactFiniteLimit ell c n where
  toFun x := ⟨fun r ↦ compactReduction ell c n r x,
    fun r ↦ compactReductionsCommute ell c n r x⟩
  map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
  map_add' x y := Subtype.ext (funext fun _ ↦ map_add _ x y)

end MathlibExt.AlgebraicGeometry.ContinuousAdicCompactSupports
