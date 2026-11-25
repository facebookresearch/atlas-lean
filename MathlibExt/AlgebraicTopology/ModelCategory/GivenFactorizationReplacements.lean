/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Replacements obtained from a given complete factorization record

The initial and terminal objects and their universal-property functions are
explicit inputs. The two replacement functors apply the given middle functor
to those original arrow families. Their units, counits and second endpoint
maps are the given natural factor maps. No existential factor getter or
default initial or terminal object is used.

The model-specific conclusions use an explicit model dictionary and records
classified for that dictionary. The same underlying replacement functions
can therefore be compared between two model-keyed carriers.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.GivenFactorizationReplacements

variable {C : Type u} [Category.{v} C]

/-- The caller's actual initial-arrow family, including both square components. -/
def initialArrows (Z : C) (hZ : IsInitial Z) : C ⥤ Arrow C where
  obj X := Arrow.mk (hZ.to X)
  map f := Arrow.homMk (𝟙 Z) f (hZ.hom_ext _ _)
  map_id X := by
    apply Arrow.hom_ext <;> rfl
  map_comp f g := by
    apply Arrow.hom_ext
    · exact (Category.comp_id _).symm
    · rfl

/-- The caller's actual terminal-arrow family with its original square components. -/
def terminalArrows (Z : C) (hZ : IsTerminal Z) : C ⥤ Arrow C where
  obj X := Arrow.mk (hZ.from X)
  map f := Arrow.homMk f (𝟙 Z) (hZ.hom_ext _ _)
  map_id X := by
    apply Arrow.hom_ext <;> rfl
  map_comp f g := by
    apply Arrow.hom_ext
    · rfl
    · exact (Category.comp_id _).symm

/-- The original initial endpoint maps form the complete natural transformation. -/
def initialMapNatTrans (Z : C) (hZ : IsInitial Z) : (Functor.const C).obj Z ⟶ 𝟭 C where
  app X := hZ.to X
  naturality _ _ _ := hZ.hom_ext _ _

/-- The original terminal endpoint maps form the complete natural transformation. -/
def terminalMapNatTrans (Z : C) (hZ : IsTerminal Z) : 𝟭 C ⟶ (Functor.const C).obj Z where
  app X := hZ.from X
  naturality _ _ _ := hZ.hom_ext _ _

variable {P Q : MorphismProperty C}

/-- The initial replacement is the supplied entire middle functor on the original arrows. -/
def initialReplacement (data : FunctorialFactorizationData P Q)
    (Z : C) (hZ : IsInitial Z) : C ⥤ C := initialArrows Z hZ ⋙ data.Z

/-- The terminal replacement uses the same supplied middle functor on terminal arrows. -/
def terminalReplacement (data : FunctorialFactorizationData P Q)
    (Z : C) (hZ : IsTerminal Z) : C ⥤ C := terminalArrows Z hZ ⋙ data.Z

/-- The full original I right factor is the initial replacement's projection. -/
def initialProjection (data : FunctorialFactorizationData P Q)
    (Z : C) (hZ : IsInitial Z) : initialReplacement data Z hZ ⟶ 𝟭 C where
  app X := data.p.app (Arrow.mk (hZ.to X))
  naturality _ _ f := data.p.naturality ((initialArrows Z hZ).map f)

/-- The initial replacement's other leg is the supplied full left natural factor. -/
def initialLeg (data : FunctorialFactorizationData P Q)
    (Z : C) (hZ : IsInitial Z) :
    (Functor.const C).obj Z ⟶ initialReplacement data Z hZ where
  app X := data.i.app (Arrow.mk (hZ.to X))
  naturality _ _ f := data.i.naturality ((initialArrows Z hZ).map f)

/-- The full original K left factor is the terminal replacement's unit. -/
def terminalUnit (data : FunctorialFactorizationData P Q)
    (Z : C) (hZ : IsTerminal Z) : 𝟭 C ⟶ terminalReplacement data Z hZ where
  app X := data.i.app (Arrow.mk (hZ.from X))
  naturality _ _ f := data.i.naturality ((terminalArrows Z hZ).map f)

/-- The terminal replacement's other leg is the supplied full right factor. -/
def terminalLeg (data : FunctorialFactorizationData P Q)
    (Z : C) (hZ : IsTerminal Z) :
    terminalReplacement data Z hZ ⟶ (Functor.const C).obj Z where
  app X := data.p.app (Arrow.mk (hZ.from X))
  naturality _ _ f := data.p.naturality ((terminalArrows Z hZ).map f)

/-- Both initial factor functions recover the caller's actual original initial maps. -/
theorem initial_fac (data : FunctorialFactorizationData P Q)
    (Z : C) (hZ : IsInitial Z) :
    initialLeg data Z hZ ≫ initialProjection data Z hZ = initialMapNatTrans Z hZ := by
  apply NatTrans.ext
  funext X
  exact data.fac_app

/-- Both terminal factor functions recover the caller's entire original terminal maps. -/
theorem terminal_fac (data : FunctorialFactorizationData P Q)
    (Z : C) (hZ : IsTerminal Z) :
    terminalUnit data Z hZ ≫ terminalLeg data Z hZ = terminalMapNatTrans Z hZ := by
  apply NatTrans.ext
  funext X
  exact data.fac_app

/-- Every complete initial replacement map is the original given map on that square. -/
theorem initialReplacement_map (data : FunctorialFactorizationData P Q)
    (Z : C) (hZ : IsInitial Z) {X Y : C} (f : X ⟶ Y) :
    (initialReplacement data Z hZ).map f =
      data.Z.map (Arrow.homMk (𝟙 Z) f (hZ.hom_ext _ _)) := rfl

/-- Every complete terminal replacement map is the original given map on that square. -/
theorem terminalReplacement_map (data : FunctorialFactorizationData P Q)
    (Z : C) (hZ : IsTerminal Z) {X Y : C} (f : X ⟶ Y) :
    (terminalReplacement data Z hZ).map f =
      data.Z.map (Arrow.homMk f (𝟙 Z) (hZ.hom_ext _ _)) := rfl

/-- The whole I projection square follows the same supplied middle-map function. -/
theorem initialProjection_naturality (data : FunctorialFactorizationData P Q)
    (Z : C) (hZ : IsInitial Z) {X Y : C} (f : X ⟶ Y) :
    (initialReplacement data Z hZ).map f ≫ (initialProjection data Z hZ).app Y =
      (initialProjection data Z hZ).app X ≫ f :=
  (initialProjection data Z hZ).naturality f

/-- The whole K unit square retains the same supplied middle-map function. -/
theorem terminalUnit_naturality (data : FunctorialFactorizationData P Q)
    (Z : C) (hZ : IsTerminal Z) {X Y : C} (f : X ⟶ Y) :
    f ≫ (terminalUnit data Z hZ).app Y =
      (terminalUnit data Z hZ).app X ≫ (terminalReplacement data Z hZ).map f :=
  (terminalUnit data Z hZ).naturality f

/-- Reclassification leaves the entire initial replacement functor unchanged. -/
theorem initialReplacement_ofLE {P' Q' : MorphismProperty C}
    (data : FunctorialFactorizationData P Q) (hP : P ≤ P') (hQ : Q ≤ Q')
    (Z : C) (hZ : IsInitial Z) :
    initialReplacement (data.ofLE hP hQ) Z hZ = initialReplacement data Z hZ := rfl

/-- Reclassification leaves the entire terminal replacement functor unchanged. -/
theorem terminalReplacement_ofLE {P' Q' : MorphismProperty C}
    (data : FunctorialFactorizationData P Q) (hP : P ≤ P') (hQ : Q ≤ Q')
    (Z : C) (hZ : IsTerminal Z) :
    terminalReplacement (data.ofLE hP hQ) Z hZ = terminalReplacement data Z hZ := rfl

/-- Reclassification retains the complete original initial projection family. -/
theorem initialProjection_ofLE {P' Q' : MorphismProperty C}
    (data : FunctorialFactorizationData P Q) (hP : P ≤ P') (hQ : Q ≤ Q')
    (Z : C) (hZ : IsInitial Z) :
    initialProjection (data.ofLE hP hQ) Z hZ = initialProjection data Z hZ := rfl

/-- Reclassification retains the complete original terminal unit family. -/
theorem terminalUnit_ofLE {P' Q' : MorphismProperty C}
    (data : FunctorialFactorizationData P Q) (hP : P ≤ P') (hQ : Q ≤ Q')
    (Z : C) (hZ : IsTerminal Z) :
    terminalUnit (data.ofLE hP hQ) Z hZ = terminalUnit data Z hZ := rfl

section Model

variable (m : ModelCategory C)

/-- The given I factor makes every selected initial replacement object cofibrant. -/
theorem initialReplacement_isCofibrant
    (data : FunctorialFactorizationData m.categoryWithCofibrations.cofibrations
      (m.categoryWithFibrations.fibrations ⊓
        m.categoryWithWeakEquivalences.weakEquivalences))
    (Z : C) (hZ : IsInitial Z) (X : C) :
    let : ModelCategory C := m
    IsCofibrant ((initialReplacement data Z hZ).obj X) := by
  let : ModelCategory C := m
  apply (isCofibrant_iff_of_isInitial (data.i.app (Arrow.mk (hZ.to X))) hZ).2
  exact (cofibration_iff _).2 (data.hi _)

/-- The given I projection is weak in exactly the supplied model dictionary. -/
theorem initialProjection_weak
    (data : FunctorialFactorizationData m.categoryWithCofibrations.cofibrations
      (m.categoryWithFibrations.fibrations ⊓
        m.categoryWithWeakEquivalences.weakEquivalences))
    (Z : C) (hZ : IsInitial Z) (X : C) :
    let : ModelCategory C := m
    WeakEquivalence ((initialProjection data Z hZ).app X) := by
  let : ModelCategory C := m
  exact (weakEquivalence_iff _).2 (data.hp _).2

/-- The same given I projection is a fibration in that actual model. -/
theorem initialProjection_fibration
    (data : FunctorialFactorizationData m.categoryWithCofibrations.cofibrations
      (m.categoryWithFibrations.fibrations ⊓
        m.categoryWithWeakEquivalences.weakEquivalences))
    (Z : C) (hZ : IsInitial Z) (X : C) :
    let : ModelCategory C := m
    Fibration ((initialProjection data Z hZ).app X) := by
  let : ModelCategory C := m
  exact (fibration_iff _).2 (data.hp _).1

/-- The given K factor makes every selected terminal replacement object fibrant. -/
theorem terminalReplacement_isFibrant
    (data : FunctorialFactorizationData
      (m.categoryWithCofibrations.cofibrations ⊓
        m.categoryWithWeakEquivalences.weakEquivalences)
      m.categoryWithFibrations.fibrations)
    (Z : C) (hZ : IsTerminal Z) (X : C) :
    let : ModelCategory C := m
    IsFibrant ((terminalReplacement data Z hZ).obj X) := by
  let : ModelCategory C := m
  apply (isFibrant_iff_of_isTerminal (data.p.app (Arrow.mk (hZ.from X))) hZ).2
  exact (fibration_iff _).2 (data.hp _)

/-- The original K unit is weak for every coefficient, with no cofibrancy hypothesis. -/
theorem terminalUnit_weak
    (data : FunctorialFactorizationData
      (m.categoryWithCofibrations.cofibrations ⊓
        m.categoryWithWeakEquivalences.weakEquivalences)
      m.categoryWithFibrations.fibrations)
    (Z : C) (hZ : IsTerminal Z) (X : C) :
    let : ModelCategory C := m
    WeakEquivalence ((terminalUnit data Z hZ).app X) := by
  let : ModelCategory C := m
  exact (weakEquivalence_iff _).2 (data.hi _).2

/-- The same original K unit is a cofibration in that actual model. -/
theorem terminalUnit_cofibration
    (data : FunctorialFactorizationData
      (m.categoryWithCofibrations.cofibrations ⊓
        m.categoryWithWeakEquivalences.weakEquivalences)
      m.categoryWithFibrations.fibrations)
    (Z : C) (hZ : IsTerminal Z) (X : C) :
    let : ModelCategory C := m
    Cofibration ((terminalUnit data Z hZ).app X) := by
  let : ModelCategory C := m
  exact (cofibration_iff _).2 (data.hi _).1

end Model

end HomotopicalAlgebra.GivenFactorizationReplacements
