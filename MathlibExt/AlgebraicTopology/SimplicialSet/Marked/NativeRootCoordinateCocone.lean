/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootLowerPairGluing
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootUpperPairGluing
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeLowerUpperRootInverseGluing

/-!
# The complete original marked root-coordinate inverse cocone

Every original lower and upper coordinate keeps its actual inverse
map into the same native boundary source coefficient. Genuine full
marked lower/lower, lower/upper and upper/upper equations, together
with the unchanged original coordinate swap, give every complete
original pair relation. The entire original marked coordinate
multicofork therefore has its actual source inverse cocone.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every complete original marked root-coordinate face enters the actual native source coefficient through its same
original genuine lower or upper inverse map. -/
def nativeRootCoordinateInverse (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌)
    (a : RootCoordinateIndex.{u} n) :
    coneRootCoordinateFaceWeight n a ⟶ nativeBoundarySourceRootValue B (n + 1) σ :=
  match a with
  | (⟨⟨j⟩, hj⟩, false) => nativeLowerRootBoundaryInverse B σ j hj
  | (⟨⟨j⟩, hj⟩, true) => nativeUpperRootBoundaryInverse B σ j hj

/-- Every entire original marked coordinate intersection satisfies the actual inverse cocone relation inside the
same original native source coefficient. -/
theorem nativeRootCoordinateInverse_condition (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌)
    (a b : RootCoordinateIndex.{u} n) :
    coneRootCoordinatePairLeft n a b ≫ nativeRootCoordinateInverse B n σ a =
      coneRootCoordinatePairRight n a b ≫ nativeRootCoordinateInverse B n σ b := by
  rcases a with ⟨⟨⟨j⟩, hj⟩, ε⟩
  rcases b with ⟨⟨⟨k⟩, hk⟩, δ⟩
  cases ε <;> cases δ
  · exact nativeRootLowerPair_condition B n σ j k hj hk
  · exact nativeLowerUpperRootInverse_condition B n σ j k hj hk
  · let a := coneRootUpperIndex.{u} n j hj
    let b := coneRootLowerIndex.{u} n k hk
    let e := coneRootCoordinatePairSwapIso n a b
    let f := nativeUpperRootBoundaryInverse B σ j hj
    let g := nativeLowerRootBoundaryInverse B σ k hk
    have h : coneRootCoordinatePairLeft n b a ≫ g = coneRootCoordinatePairRight n b a ≫ f :=
      nativeLowerUpperRootInverse_condition B n σ k j hk hj
    have hs : e.hom ≫ (coneRootCoordinatePairLeft n b a ≫ g) =
        e.hom ≫ (coneRootCoordinatePairRight n b a ≫ f) := congrArg (fun p => e.hom ≫ p) h
    have hl : e.hom ≫ (coneRootCoordinatePairLeft n b a ≫ g) = coneRootCoordinatePairRight n a b ≫ g :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun p => p ≫ g) (coneRootCoordinatePairSwapIso_left n a b))
    have hr : e.hom ≫ (coneRootCoordinatePairRight n b a ≫ f) = coneRootCoordinatePairLeft n a b ≫ f :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun p => p ≫ f) (coneRootCoordinatePairSwapIso_right n a b))
    exact hr.symm.trans (hs.symm.trans hl)
  · exact nativeRootUpperPair_condition B n σ j k hj hk

/-- The same entire original marked coordinate-face and full-intersection multispan is retained at the original root. -/
abbrev nativeRootCoordinateSpan (n : ℕ) :=
  (coneCoordinateBoundaryDiagram (⊥ : Vertex.{u} (n + 1))).multispanIndex.map
    (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 1))))

/-- All original whole marked root-coordinate inverse maps give the actual complete original multicofork into the
same native boundary source root coefficient. -/
def nativeRootCoordinateInverseCocone (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    Multicofork (nativeRootCoordinateSpan.{u} n) :=
  Multicofork.ofπ _ (nativeBoundarySourceRootValue B (n + 1) σ)
    (nativeRootCoordinateInverse B n σ)
    (fun p => nativeRootCoordinateInverse_condition B n σ p.1 p.2)

end SSet.Marked
