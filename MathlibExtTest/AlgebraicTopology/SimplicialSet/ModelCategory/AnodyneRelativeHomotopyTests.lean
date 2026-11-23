/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AnodyneRelativeHomotopy

/-!
# Tests for relative homotopy extension across anodyne maps

Public-only clients exercise both endpoints, the relative stationarity law,
isomorphisms, a genuine horn inclusion, the empty simplicial set, and all
required universe levels.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Simplicial
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace AnodyneRelativeHomotopyTests

universe u

private theorem endpointAndStationarityClient
    {X Y K : SSet.{u}} {i : X ⟶ Y}
    (hi : SSet.anodyneExtensions i) [SSet.KanComplex K]
    {a b : Y ⟶ K} (hab : i ≫ a = i ≫ b) :
    ∃ H : SSet.Homotopy a b,
      SSet.ι₀ ≫ H.h = a ∧
        SSet.ι₁ ≫ H.h = b ∧
          (i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
            fst X (Δ[1] : SSet.{u}) ≫ i ≫ a := by
  obtain ⟨H, hrel⟩ := hi.exists_homotopy_rel hab
  exact ⟨H, H.h₀, H.h₁, hrel⟩

section SymbolicUniverse

variable {X Y K : SSet.{u}} {i : X ⟶ Y}
  (hi : SSet.anodyneExtensions i) [SSet.KanComplex K]
  {a b : Y ⟶ K} (hab : i ≫ a = i ≫ b)

example :
    ∃ H : SSet.Homotopy a b,
      SSet.ι₀ ≫ H.h = a ∧
        SSet.ι₁ ≫ H.h = b ∧
          (i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
            fst X (Δ[1] : SSet.{u}) ≫ i ≫ a :=
  endpointAndStationarityClient hi hab

/-- The public theorem consumes equality after precomposition; no global
equality `a = b` is needed or derivable by type conversion. -/
example : Nonempty (SSet.Homotopy a b) := by
  fail_if_success
    have _h : a = b := hab
  obtain ⟨H, _⟩ := hi.exists_homotopy_rel hab
  exact ⟨H⟩

end SymbolicUniverse

section Isomorphisms

example (X K : SSet.{u}) [SSet.KanComplex K] (a : X ⟶ K) :
    ∃ H : SSet.Homotopy a a,
      SSet.ι₀ ≫ H.h = a ∧
        SSet.ι₁ ≫ H.h = a ∧
          ((𝟙 X) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
            fst X (Δ[1] : SSet.{u}) ≫ 𝟙 X ≫ a :=
  endpointAndStationarityClient
    (SSet.anodyneExtensions.of_isIso (𝟙 X)) rfl

example {X Y K : SSet.{u}} (e : X ≅ Y) [SSet.KanComplex K]
    {a b : Y ⟶ K} (hab : e.hom ≫ a = e.hom ≫ b) :
    Nonempty (SSet.Homotopy a b) := by
  obtain ⟨H, _⟩ :=
    SSet.anodyneExtensions.exists_homotopy_rel
      (SSet.anodyneExtensions.of_isIso e.hom) hab
  exact ⟨H⟩

end Isomorphisms

section HornExtension

example {K : SSet.{u}} [SSet.KanComplex K]
    {a b : (Δ[1] : SSet.{u}) ⟶ K}
    (hab : (SSet.horn 1 (0 : Fin 2)).ι ≫ a =
      (SSet.horn 1 (0 : Fin 2)).ι ≫ b) :
    ∃ H : SSet.Homotopy a b,
      SSet.ι₀ ≫ H.h = a ∧
        SSet.ι₁ ≫ H.h = b ∧
          ((SSet.horn 1 (0 : Fin 2)).ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
            fst (SSet.horn 1 (0 : Fin 2) : SSet.{u}) Δ[1] ≫
              (SSet.horn 1 (0 : Fin 2)).ι ≫ a :=
  endpointAndStationarityClient
    (SSet.anodyneExtensions.horn_ι (0 : Fin 2)) hab

end HornExtension

section EmptySource

private abbrev emptySSet : SSet.{u} :=
  (⊥ : (Δ[0] : SSet.{u}).Subcomplex)

example {K : SSet.{u}} [SSet.KanComplex K] (a : emptySSet ⟶ K) :
    Nonempty (SSet.Homotopy a a) := by
  obtain ⟨H, _⟩ :=
    SSet.anodyneExtensions.exists_homotopy_rel
      (SSet.anodyneExtensions.of_isIso (𝟙 emptySSet))
      (a := a) (b := a) rfl
  exact ⟨H⟩

end EmptySource

section ExplicitUniverses

example {X Y K : SSet.{1}} {i : X ⟶ Y}
    (hi : SSet.anodyneExtensions i) [SSet.KanComplex K]
    {a b : Y ⟶ K} (hab : i ≫ a = i ≫ b) :
    Nonempty (SSet.Homotopy a b) := by
  obtain ⟨H, _⟩ := hi.exists_homotopy_rel hab
  exact ⟨H⟩

example {X Y K : SSet.{0}} {i : X ⟶ Y}
    (hi : SSet.anodyneExtensions i) [SSet.KanComplex K]
    {a b : Y ⟶ K} (hab : i ≫ a = i ≫ b) :
    Nonempty (SSet.Homotopy a b) := by
  obtain ⟨H, _⟩ := hi.exists_homotopy_rel hab
  exact ⟨H⟩

end ExplicitUniverses

section PrivateBoundary

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.endpointMap

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.anodyneExtensions_mono

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.range_ι_mem_anodyneExtensions

end PrivateBoundary

#print axioms SSet.anodyneExtensions.exists_homotopy_rel

end AnodyneRelativeHomotopyTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet
