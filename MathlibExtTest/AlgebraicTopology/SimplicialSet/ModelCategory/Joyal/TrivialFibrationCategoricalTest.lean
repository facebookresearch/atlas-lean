/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.TrivialFibrationCategorical

/-!
# Trivial Kan fibrations and categorical equivalences (the supporting result): tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.TrivialFibrationCategorical`:
the coherent cylinder homotopy over a trivial Kan fibration
(`SSet.exists_homotopy_over_of_rlp_I`), the packaged section and coherent
homotopies (`SSet.exists_section_and_homotopies_of_rlp_I`), the formal
assembly step
(`SSet.categoricalEquivalences.of_section_of_hoPre_id_natIso`), and the
edge dictionary for functor objects (`SSet.Homotopy.edgeIhom` and
`SSet.Homotopy.edgeIhom_edge`, of the neutral module
`MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyIhom` and
re-exported by the main file), at an arbitrary universe and at
universe `0`.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace TrivialFibrationCategoricalTest

section CoherentHomotopy

variable {X Y : SSet.{u}} {p : X ⟶ Y} {a b : X ⟶ X}

example (hp : SSet.modelCategoryQuillen.I.rlp p) (hab : a ≫ p = b ≫ p) :
    ∃ H : SSet.Homotopy a b,
      H.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ (a ≫ p) :=
  SSet.exists_homotopy_over_of_rlp_I hp hab

example (hp : SSet.modelCategoryQuillen.I.rlp p) :
    ∃ s : Y ⟶ X, s ≫ p = 𝟙 Y ∧
      (∃ H : SSet.Homotopy (𝟙 X) (p ≫ s),
        H.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ p) ∧
      (∃ H : SSet.Homotopy (p ≫ s) (𝟙 X),
        H.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ p) :=
  SSet.exists_section_and_homotopies_of_rlp_I hp

-- The coherent homotopy is a homotopy from `a` to `b`: its endpoints are
-- `a` and `b`, by the upstream endpoint lemmas for `SSet.Homotopy`.
example (hp : SSet.modelCategoryQuillen.I.rlp p) (hab : a ≫ p = b ≫ p) :
    ∃ H : SSet.Homotopy a b, SSet.ι₀ ≫ H.h = a ∧ SSet.ι₁ ≫ H.h = b := by
  obtain ⟨H, _⟩ := SSet.exists_homotopy_over_of_rlp_I hp hab
  exact ⟨H, H.h₀, H.h₁⟩

example {X₀ Y₀ : SSet.{0}} {p₀ : X₀ ⟶ Y₀}
    (hp : SSet.modelCategoryQuillen.I.rlp p₀) :
    ∃ s : Y₀ ⟶ X₀, s ≫ p₀ = 𝟙 Y₀ ∧
      Nonempty (SSet.Homotopy (𝟙 X₀) (p₀ ≫ s)) := by
  obtain ⟨s, hs, ⟨H, _⟩, _⟩ := SSet.exists_section_and_homotopies_of_rlp_I hp
  exact ⟨s, hs, ⟨H⟩⟩

end CoherentHomotopy

section Assembly

variable {X Y : SSet.{u}} {p : X ⟶ Y} {s : Y ⟶ X}

example (hs : s ≫ p = 𝟙 Y)
    (H : ∀ (C : SSet.{u}), SSet.Quasicategory C →
      Nonempty (𝟭 (SSet.hoFunctor.obj ((ihom X).obj C)) ≅
        (SSet.hoFunctor.map ((pre (p ≫ s)).app C)).toFunctor)) :
    SSet.categoricalEquivalences p :=
  SSet.categoricalEquivalences.of_section_of_hoPre_id_natIso hs H

-- The assembly applied to an isomorphism: precomposition with
-- `p ≫ s = 𝟙 X` is the identity functor by `SSet.hoFunctor_pre_id`, so
-- the natural-isomorphism hypothesis is discharged definitionally and
-- the conclusion recovers `SSet.categoricalEquivalences.of_isIso`.
example (hs : s ≫ p = 𝟙 Y) (hps : p ≫ s = 𝟙 X) :
    SSet.categoricalEquivalences p := by
  apply SSet.categoricalEquivalences.of_section_of_hoPre_id_natIso hs
  intro C _
  rw [hps, SSet.hoFunctor_pre_id]
  exact ⟨Iso.refl _⟩

-- The section of an isomorphism also satisfies the assembly's hypotheses
-- symmetrically, hence is a categorical equivalence.
example (hs : s ≫ p = 𝟙 Y) (hps : p ≫ s = 𝟙 X) :
    SSet.categoricalEquivalences s := by
  apply SSet.categoricalEquivalences.of_section_of_hoPre_id_natIso
    (p := s) (s := p) hps
  intro C _
  rw [hs, SSet.hoFunctor_pre_id]
  exact ⟨Iso.refl _⟩

end Assembly

section EdgeDictionary

variable {X C : SSet.{u}} {f g : X ⟶ C} (K : SSet.Homotopy f g)

example : ((ihom X).obj C).Edge (SSet.ihomVertexEquiv X C f)
    (SSet.ihomVertexEquiv X C g) :=
  K.edgeIhom

example : K.edgeIhom.edge =
    SSet.yonedaEquiv (MonoidalClosed.curry K.h) :=
  SSet.Homotopy.edgeIhom_edge K

-- The edge has the expected faces: these are the two endpoint conditions
-- of `SSet.Edge` at the vertices classified by `f` and `g`.
example : ((ihom X).obj C).δ (1 : Fin 2) K.edgeIhom.edge =
    SSet.ihomVertexEquiv X C f :=
  K.edgeIhom.src_eq

example : ((ihom X).obj C).δ (0 : Fin 2) K.edgeIhom.edge =
    SSet.ihomVertexEquiv X C g :=
  K.edgeIhom.tgt_eq

-- The morphism in the homotopy category of the functor object determined
-- by the edge goes between the objects determined by `f` and `g`.
example : SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv X C f) ⟶
    SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv X C g) :=
  SSet.HomotopyCategory.homMk K.edgeIhom

example {X₀ C₀ : SSet.{0}} {f₀ g₀ : X₀ ⟶ C₀} (K₀ : SSet.Homotopy f₀ g₀) :
    K₀.edgeIhom.edge =
      SSet.yonedaEquiv (MonoidalClosed.curry K₀.h) :=
  SSet.Homotopy.edgeIhom_edge K₀

end EdgeDictionary

end TrivialFibrationCategoricalTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal

end
