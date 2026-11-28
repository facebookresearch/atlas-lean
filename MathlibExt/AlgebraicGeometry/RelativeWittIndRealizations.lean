/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeWittSpaceStages
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Normalized increasing ind-realizations of the original Witt lattices

The bounded diagram uses the actual inclusions of unchanged lattice
submodules. Its cocone targets the original full lattice functor. The
space diagram uses the actual closed transition maps from the native
etale quotient presentations. Its point dictionary is the normalized
stage-by-stage natural isomorphism on all perfect residue algebras.

The ind-realization is an isomorphism of the actual sheaf colimit with
the original fpqc lattice sheaf; every colimit insertion is fixed by
the original bounded-lattice inclusion. No ind-Grassmannian alias or
unrelated colimit map is assumed.

Source: Zhu, arXiv:1407.8519v3, Theorems 0.1 and 1.4, pp. 3 and 9.
Constructors and their colimit proofs remain separate Wanted requests.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeWittIndRealizations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeWittLoopTests RelativeWittLatticeModels RelativeWittSpaceStages

variable (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k]

/-- Native fpqc sheafification of the original perfect-algebra point diagram. -/
def sheafification : (PerfectAlgebra p k ⥤ Type 1) ⥤
    Sheaf (fpqcTopology p k) (Type 1) where
  obj F := (presheafToSheaf (fpqcTopology p k) (Type 1)).obj
    ((opOpEquivalence (PerfectAlgebra p k)).functor ⋙ F)
  map f := (presheafToSheaf (fpqcTopology p k) (Type 1)).map
    (Functor.whiskerLeft (opOpEquivalence (PerfectAlgebra p k)).functor f)
  map_id F := by simp
  map_comp f g := by simp

variable (B : Type) [CommRing B] [Algebra (WittVector p k) B] (pi : B)
  (n : ℕ) (D : ScalarExtension p k B pi n)

/-- The original full lattice sheaf, with its prescribed scalar maps. -/
def latticeSheaf := (sheafification p k).obj D.functor

variable {p k B pi n}
variable {D}

/-- The increasing bounded diagram is made from the original inclusions. -/
def boundedDiagram (D : ScalarExtension p k B pi n) :
    ℕ ⥤ (PerfectAlgebra p k ⥤ Type 1) where
  obj N := D.boundedFunctor N
  map f := D.transition (leOfHom f)
  map_id N := by
    apply NatTrans.ext
    funext R
    apply ConcreteCategory.hom_ext
    intro L
    apply ULift.ext
    apply Subtype.ext
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext R
    apply ConcreteCategory.hom_ext
    intro L
    apply ULift.ext
    apply Subtype.ext
    rfl

/-- The bounded point is sent to its very same original lattice. -/
def boundedInclusion (D : ScalarExtension p k B pi n) (N : ℕ) :
    D.boundedFunctor N ⟶ D.functor where
  app R := ↾fun L ↦ ULift.up L.down.val
  naturality {R S} f := by
    apply ConcreteCategory.hom_ext
    intro L
    rfl

/-- The literal cocone of all original bounded-lattice inclusions. -/
def boundedPresheafCocone (D : ScalarExtension p k B pi n) :
    Cocone (boundedDiagram D) where
  pt := D.functor
  ι :=
    { app := boundedInclusion D
      naturality := by
        intro N M f
        apply NatTrans.ext
        funext R
        apply ConcreteCategory.hom_ext
        intro L
        rfl }

/-- Its actual fpqc sheaf cocone, using the same sheafification functor. -/
def boundedSheafCocone (D : ScalarExtension p k B pi n) :=
  (sheafification p k).mapCocone (boundedPresheafCocone D)

/-- Actual algebraic-space points of the increasing closed stage maps. -/
def pointsDiagram (S : IndLatticeStages p k B pi n D) :
    ℕ ⥤ (PerfectAlgebra p k ⥤ Type 1) where
  obj N := spacePoints p k (S.stage N).perfection.space
  map f := spacePointMap p k (S.transition (leOfHom f))
  map_id N := by
    rw [S.identity]
    apply NatTrans.ext
    funext R
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl
  map_comp f g := by
    have h := S.composition (leOfHom f) (leOfHom g)
    rw [h]
    apply NatTrans.ext
    funext R
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl

/-- The stage point dictionary retains all original bounded transition squares. -/
def pointDictionary (S : IndLatticeStages p k B pi n D) :
    boundedDiagram D ≅ pointsDiagram S :=
  NatIso.ofComponents (fun N ↦ (S.stage N).points)
    (fun f ↦ S.normalized (leOfHom f))

/-- The native sheaf colimit diagram of actual algebraic-space stages. -/
def spaceSheafDiagram (S : IndLatticeStages p k B pi n D) :=
  pointsDiagram S ⋙ sheafification p k

/-- An ind-realization is pinned on every original bounded lattice insertion. -/
structure IndRealization (S : IndLatticeStages p k B pi n D) where
  comparison : colimit (spaceSheafDiagram S) ≅ latticeSheaf p k B pi n D
  normalized : ∀ N : ℕ,
    colimit.ι (spaceSheafDiagram S) N ≫ comparison.hom =
      (sheafification p k).map (S.stage N).points.inv ≫
        (boundedSheafCocone D).ι.app N

end MathlibExt.AlgebraicGeometry.RelativeWittIndRealizations
