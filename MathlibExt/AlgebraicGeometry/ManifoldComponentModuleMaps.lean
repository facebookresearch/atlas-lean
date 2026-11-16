/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HolomorphicSheafHiggsModels
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Native restriction and assembly on connected manifold components

A component partition is a finite disjoint cover by actual connected
clopen sets. Restriction is the native over-site module functor, with
the actual restricted ring of functions. Assembly is the finite product
of the native component pushforwards. The comparison from E to its
assembled restrictions is built from the native adjunction units.

Every module operator, including theta, restricts by the same actual
functor. The connected/nonempty Higgs comparison can therefore be used
componentwise. The component equivalence/gluing proofs are separate
Wanted requests; a disconnected correspondence is not declared here.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ManifoldComponentModuleMaps

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open KahlerClassGeometry HarmonicHolomorphicModuleModels HolomorphicCotangentModuleModels
open HolomorphicSheafHiggsModels
open scoped Manifold ContDiff

variable {M : Type} [TopologicalSpace M]

/-- The actual finite component decomposition, with all connected clopen subsets and their cover. -/
structure FiniteComponentPartition where
  count : ℕ
  component : Fin count → Opens M
  connected : ∀ i, IsConnected (component i : Set M)
  closed : ∀ i, IsClosed (component i : Set M)
  disjoint : ∀ i j, i ≠ j → Disjoint (component i : Set M) (component j : Set M)
  covers : ∀ x : M, ∃ i : Fin count, x ∈ component i

variable {n : ℕ} [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  [HolomorphicCoefficientSheaves.SheafCondition (Coordinates n) M]
  [CotangentSectionCalculus (n := n) (M := M)] [CotangentSheafCondition (n := n) (M := M)]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- The actual over-site coefficient module on the component, retaining the restricted holomorphic ring. -/
abbrev ComponentModules (U : Opens M) :=
  SheafOfModules.{0} ((holomorphicStructureRing (n := n) (M := M)).over U)

/-- Native component restriction acts on every actual module and every actual O-linear operator. -/
def componentRestriction (U : Opens M) : HolomorphicModules (n := n) (M := M) ⥤ ComponentModules (n := n) U :=
  SheafOfModules.overFunctor (holomorphicStructureRing (n := n) (M := M)) U

/-- The native right adjoint is the actual over-star pushforward with the original ring restriction map. -/
def componentPushforward (U : Opens M) : ComponentModules (n := n) U ⥤ HolomorphicModules (n := n) (M := M) :=
  SheafOfModules.pushforward
    (SheafOfModules.pushforwardOver (R := holomorphicStructureRing (n := n) (M := M)) U)

/-- The actual native component restriction/pushforward adjunction. -/
def componentAdjunction (U : Opens M) : componentRestriction (n := n) U ⊣ componentPushforward (n := n) U :=
  SheafOfModules.overPushforwardOverAdj (R := holomorphicStructureRing (n := n) (M := M)) U

/-- Assembly is the native finite product of the actual component pushforwards. -/
def assembleComponents (P : FiniteComponentPartition (M := M))
    (E : ∀ i : Fin P.count, ComponentModules (n := n) (P.component i)) : HolomorphicModules (n := n) (M := M) :=
  limit (Discrete.functor (fun i : Fin P.count => (componentPushforward (n := n) (P.component i)).obj (E i)))

/-- The comparison uses every native adjunction unit, preserving the actual module on each component. -/
def componentAssemblyUnit (P : FiniteComponentPartition (M := M))
    (E : HolomorphicModules (n := n) (M := M)) : E ⟶
    assembleComponents (n := n) P (fun i => (componentRestriction (n := n) (P.component i)).obj E) :=
  limit.lift (Discrete.functor (fun i : Fin P.count =>
    (componentPushforward (n := n) (P.component i)).obj
      ((componentRestriction (n := n) (P.component i)).obj E))) {
    pt := E
    π := {
      app i := (componentAdjunction (n := n) (P.component i.as)).unit.app E
      naturality i j f := by
        have h : i.as = j.as := Discrete.eq_of_hom f
        have hij : i = j := congrArg Discrete.mk h
        subst j
        have hf : f = 𝟙 i := Subsingleton.elim _ _
        subst f
        simp } }

/-- Every actual global operator restricts by the same native over-site functor. -/
def restrictOperator {E F : HolomorphicModules (n := n) (M := M)} (U : Opens M) (a : E ⟶ F) :
    (componentRestriction (n := n) U).obj E ⟶ (componentRestriction (n := n) U).obj F :=
  (componentRestriction (n := n) U).map a

end MathlibExt.AlgebraicGeometry.ManifoldComponentModuleMaps
