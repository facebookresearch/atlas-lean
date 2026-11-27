/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeWittCoefficientDVRModels
public import MathlibExt.AlgebraicGeometry.GeneralStackGeometry
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual algebraic-space stages for the relative Witt lattice functor

An algebraic space retains its native fppf sheaf and actual etale
equivalence presentation from `GeneralStackGeometry`. Perfectness is
tested on the actual affine-open section rings of its etale atlas.
Perfection maps have the universal property on every perfect scheme test.
No arbitrary space, point set or transition functor is selected.

The ordinary proper model retains finite presentation, the quotient
topology of the actual atlas relation, the closed relative diagonal, and
the valuative lifting property on all valuation rings. Closed transitions
are representable by actual scheme pullback cones on every scheme test.
These definitions express the ordinary algebraic-space properness and
perfection in Zhu's statement; constructors and the lattice dictionary
are separate Wanted requests.

Source: Zhu, arXiv:1407.8519v3, Theorem 0.1, p. 3,
Theorem 1.4, p. 9, Proposition 1.12, p. 13, and Appendix A.
The completed etale quotient integration is attributed in the imported
`EtaleSpacePresentations` and `GeneralStackGeometry` source closure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeWittSpaceStages

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.GeneralStackGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations
open RelativeWittLoopTests RelativeWittLatticeModels

variable (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k]

/-- All spaces have their original structural map to the residue base. -/
abbrev Space := AlgebraicSpaceOver (Spec (.of k))

/-- The native over-category object retains the actual quotient sheaf. -/
def asOver (A : Space k) : Over (represented.obj (Spec (.of k))) :=
  Over.mk A.structural

/-- A space map is an actual structural-compatible fppf sheaf map. -/
abbrev SpaceMap (A C : Space k) := asOver k A ⟶ asOver k C

variable {p k}

/-- The map on actual sections is induced by the original sheaf map. -/
def relativeMap {A C : Space k} (f : SpaceMap k A C) :
    A.relativePresheaf ⟶ C.relativePresheaf where
  app V := ↾fun x ↦ ⟨f.left.hom.app (op V.unop.left) x.val, by
    have h := congrArg (fun q ↦ q.hom.app (op V.unop.left) x.val) (Over.w f)
    exact h.trans x.property⟩
  naturality {V W} a := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (f.left.hom.naturality a.unop.left.op) x.val

variable (p k)

/-- Perfectness is the actual Frobenius condition on every affine chart: the sections have
characteristic `p` and their Frobenius is bijective. (Over an arbitrary base the characteristic
condition is not automatic: cubing is bijective on `𝔽₂`.) -/
def IsPerfectScheme (T : Over (Spec (.of k))) : Prop :=
  ∀ U : T.left.Opens, IsAffineOpen U →
    (p : Γ(T.left, U)) = 0 ∧ Function.Bijective (fun a : Γ(T.left, U) ↦ a ^ p)

/-- The chosen etale atlas has actual perfect affine-open section rings of characteristic `p`. -/
def IsPerfectSpace (A : Space k) : Prop :=
  ∀ U : A.presentation.U.Opens, IsAffineOpen U →
    (p : Γ(A.presentation.U, U)) = 0 ∧
      Function.Bijective (fun a : Γ(A.presentation.U, U) ↦ a ^ p)

/-- An ordinary space and its universal actual perfect realization. -/
structure Perfection (A : Space k) where
  space : Space k
  perfect : IsPerfectSpace p k space
  projection : SpaceMap k space A
  universal : ∀ T : Over (Spec (.of k)), IsPerfectScheme p k T →
    Function.Bijective ((relativeMap projection).app (op T))

/-- Every residue-algebra test retains its native affine structural map. -/
def residueTests : (PerfectAlgebra p k)ᵒᵖ ⥤ Over (Spec (.of k)) where
  obj R := Over.mk (Spec.algebraMap k R.unop.obj)
  map {R S} f := Over.homMk
    (Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom)) (by
      change Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k S.unop.obj)) =
          Spec.map (CommRingCat.ofHom (algebraMap k R.unop.obj))
      rw [← Spec.map_comp]
      congr 1
      ext a
      exact f.unop.hom.hom.commutes a)
  map_id R := by
    apply Over.OverMorphism.ext
    change Spec.map (𝟙 (CommRingCat.of R.unop.obj)) = 𝟙 _
    exact Spec.map_id _
  map_comp f g := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (f ≫ g).unop.hom.hom.toRingHom) =
      Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom)
    rw [← Spec.map_comp]
    rfl

/-- Points are the original quotient sheaf sections over the actual test. -/
def spacePoints (A : Space k) : PerfectAlgebra p k ⥤ Type 1 :=
  (residueTests p k).rightOp ⋙ A.relativePresheaf

/-- Space maps use the same section map on every perfect test algebra. -/
def spacePointMap {A C : Space k} (f : SpaceMap k A C) :
    spacePoints p k A ⟶ spacePoints p k C :=
  Functor.whiskerLeft (residueTests p k).rightOp (relativeMap f)

variable {p}

/-- The topology is the quotient of the actual etale atlas point relation. -/
abbrev TopologicalPoints (A : Space k) :=
  Quotient (Relation.EqvGen.setoid (fun x y : A.presentation.U ↦
    ∃ r : A.presentation.R, A.presentation.source r = x ∧ A.presentation.target r = y))

/-- The generic-point arrow is the actual spectrum map of the fraction algebra. -/
def genericTestMap (V K : Type) [CommRing V] [Field K]
    [Algebra k V] [Algebra V K] [Algebra k K] [IsScalarTower k V K] :
    Over.mk (Spec.algebraMap k K) ⟶ Over.mk (Spec.algebraMap k V) :=
  Over.homMk (Spec.algebraMap V K) (by
    change Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k V)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K))
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact (IsScalarTower.algebraMap_apply k V K a).symm)

/-- Actual finite-presentation, quasi-compact, separated valuative properness. -/
structure ProperModel (A : Space k) where
  chart : A.Chart
  relation_over_base :
    A.presentation.source ≫ chart.map = A.presentation.target ≫ chart.map
  [presentation : LocallyOfFinitePresentation chart.map]
  [compact : CompactSpace (TopologicalPoints k A)]
  [diagonal : IsClosedImmersion
    (pullback.lift A.presentation.source A.presentation.target relation_over_base)]
  valuative : ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra k V] [Algebra V K] [IsFractionRing V K]
    [Algebra k K] [IsScalarTower k V K],
    Function.Bijective (A.relativePresheaf.map (genericTestMap k V K).op)

/-- A scheme fibre is its actual pullback cone, with the original maps. -/
structure SchemeFibre {A C : Space k} (f : SpaceMap k A C)
    (V : Scheme) (y : represented.obj V ⟶ C.sheaf) where
  scheme : Over V
  map : represented.obj scheme.left ⟶ A.sheaf
  commutes : map ≫ f.left = represented.map scheme.hom ≫ y
  universal : IsLimit (PullbackCone.mk map (represented.map scheme.hom) commutes)

/-- Closedness on every actual scheme fibre, with no arbitrary atlas condition. -/
def IsClosedSpaceMap {A C : Space k} (f : SpaceMap k A C) : Prop :=
  ∀ (V : Scheme) (y : represented.obj V ⟶ C.sheaf),
    ∃ F : SchemeFibre k f V y, IsClosedImmersion F.scheme.hom

variable (p) (B : Type) [CommRing B] [Algebra (WittVector p k) B] (pi : B)
  (n : ℕ) (D : ScalarExtension p k B pi n)

/-- A stage represents precisely the bounded original lattice functor. -/
structure LatticeStage (N : ℕ) where
  ordinary : Space k
  proper : ProperModel k ordinary
  perfection : Perfection p k ordinary
  points : D.boundedFunctor N ≅ spacePoints p k perfection.space

/-- Increasing closed stages retain every native lattice transition square. -/
structure IndLatticeStages where
  stage : ∀ N : ℕ, LatticeStage p k B pi n D N
  transition : ∀ {N M : ℕ}, N ≤ M →
    SpaceMap k (stage N).perfection.space (stage M).perfection.space
  identity : ∀ N, transition (le_refl N) = 𝟙 _
  composition : ∀ {N M L : ℕ} (h : N ≤ M) (j : M ≤ L),
    transition (h.trans j) = transition h ≫ transition j
  closed : ∀ {N M : ℕ} (h : N ≤ M), IsClosedSpaceMap k (transition h)
  normalized : ∀ {N M : ℕ} (h : N ≤ M),
    D.transition h ≫ (stage M).points.hom =
      (stage N).points.hom ≫ spacePointMap p k (transition h)

end MathlibExt.AlgebraicGeometry.RelativeWittSpaceStages
