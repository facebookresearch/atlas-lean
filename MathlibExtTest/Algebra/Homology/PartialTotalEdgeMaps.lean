/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalEdgeMaps

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian.SpectralObject

universe v u

namespace MathlibExtTest.Algebra.Homology.PartialTotalEdgeMaps

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

example (q : ℕ) :
    B.partialTotalFirstPageChoice.pageTwo.X (0, q) ⟶
      B.partialTotalStableObj q 0 :=
  B.partialTotalZeroColumnPageToStable q

example (q : ℕ) :
    B.partialTotalFirstPageChoice.pageTwo.X (0, q) ⟶
      (B.total (ComplexShape.down ℕ)).homology q :=
  B.partialTotalZeroColumnEdge q

example (p : ℕ) :
    B.partialTotalStableObj p p ⟶
      ((B.partialTotalSpectralObject.spectralSequence core).page (2 : ℤ)).X
        (p, 0) :=
  B.partialTotalTopRowStableToPage p

example (p : ℕ) :
    (B.total (ComplexShape.down ℕ)).homology p ⟶
      ((B.partialTotalSpectralObject.spectralSequence core).page (2 : ℤ)).X
        (p, 0) :=
  B.partialTotalTopRowEdge p

/-! ## Literal zero-degree boundaries -/

example :
    B.partialTotalFirstPageChoice.pageTwo.X (0, 0) ⟶
      B.partialTotalStableObj 0 0 :=
  B.partialTotalZeroColumnPageToStable 0

example :
    B.partialTotalFirstPageChoice.pageTwo.X (0, 0) ⟶
      (B.total (ComplexShape.down ℕ)).homology 0 :=
  B.partialTotalZeroColumnEdge 0

example :
    B.partialTotalStableObj 0 0 ⟶
      ((B.partialTotalSpectralObject.spectralSequence core).page (2 : ℤ)).X
        (0, 0) :=
  B.partialTotalTopRowStableToPage 0

example :
    (B.total (ComplexShape.down ℕ)).homology 0 ⟶
      ((B.partialTotalSpectralObject.spectralSequence core).page (2 : ℤ)).X
        (0, 0) :=
  B.partialTotalTopRowEdge 0

/-! ## The zero bicomplex -/

example (q : ℕ) :=
  HomologicalComplex₂.partialTotalZeroColumnPageToStable
    (B := (HomologicalComplex.zero : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))) q

example (q : ℕ) :=
  HomologicalComplex₂.partialTotalZeroColumnEdge
    (B := (HomologicalComplex.zero : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))) q

example (p : ℕ) :=
  HomologicalComplex₂.partialTotalTopRowStableToPage
    (B := (HomologicalComplex.zero : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))) p

example (p : ℕ) :=
  HomologicalComplex₂.partialTotalTopRowEdge
    (B := (HomologicalComplex.zero : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))) p

example (q : ℕ) : C :=
  B.partialTotalZeroColumnStableSource q

example (q : ℕ) :
    B.partialTotalZeroColumnStableSource q ≅
      B.partialTotalFirstPageChoice.pageTwoCoordinate 0 q :=
  B.partialTotalZeroColumnPageTwoLeftIso q

example (q : ℕ) :
    B.partialTotalZeroColumnStableSource q ⟶
      B.partialTotalStableObj q 0 :=
  B.partialTotalZeroColumnStableTail q

example (q : ℕ) :
    let χ := B.partialTotalFirstPageChoice
    let η := χ.pageTransitionIndex 0 q
    let Y := B.partialTotalSpectralObject
    Y.E (homOfLE η.hiBot₁) (homOfLE η.hi₁₂)
        (homOfLE (η.hi₂₃'.trans η.hi₃'Top))
        η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ ≅
      B.partialTotalStableObj q 0 :=
  B.partialTotalZeroColumnStableTargetIso q

example (q : ℕ) :
    B.partialTotalFirstPageChoice.pageTwo.X (0, q) ⟶
      B.partialTotalStableObj q 0 :=
  B.partialTotalZeroColumnPageToStable q

example (q : ℕ) :
    B.partialTotalZeroColumnPageToStable q =
      (B.partialTotalFirstPageChoice.pageTwoCoordinateIso 0 q).hom ≫
        (B.partialTotalZeroColumnPageTwoLeftIso q).inv ≫
        B.partialTotalZeroColumnStableTail q :=
  B.partialTotalZeroColumnPageToStable_eq_pageTwoCoordinate q

example {Z : C} (q : ℕ) (f : B.partialTotalStableObj q 0 ⟶ Z) :
    B.partialTotalZeroColumnPageToStable q ≫ f =
      (B.partialTotalFirstPageChoice.pageTwoCoordinateIso 0 q).hom ≫
        (B.partialTotalZeroColumnPageTwoLeftIso q).inv ≫
        B.partialTotalZeroColumnStableTail q ≫ f :=
  B.partialTotalZeroColumnPageToStable_eq_pageTwoCoordinate_assoc q f

example (q : ℕ) :
    B.partialTotalFirstPageChoice.pageTwo.X (0, q) ⟶
      (B.total (ComplexShape.down ℕ)).homology q :=
  B.partialTotalZeroColumnEdge q

example :
    B.partialTotalFirstPageChoice.pageTwo.X (0, 0) ⟶
      B.partialTotalStableObj 0 0 :=
  B.partialTotalZeroColumnPageToStable 0

example :
    B.partialTotalFirstPageChoice.pageTwo.X (0, 1) ⟶
      B.partialTotalStableObj 1 0 :=
  B.partialTotalZeroColumnPageToStable 1

example :
    B.partialTotalZeroColumnPageToStable 0 =
      (B.partialTotalFirstPageChoice.pageTwoCoordinateIso 0 0).hom ≫
        (B.partialTotalZeroColumnPageTwoLeftIso 0).inv ≫
        B.partialTotalZeroColumnStableTail 0 :=
  B.partialTotalZeroColumnPageToStable_eq_pageTwoCoordinate 0

example :
    B.partialTotalZeroColumnPageToStable 1 =
      (B.partialTotalFirstPageChoice.pageTwoCoordinateIso 0 1).hom ≫
        (B.partialTotalZeroColumnPageTwoLeftIso 1).inv ≫
        B.partialTotalZeroColumnStableTail 1 :=
  B.partialTotalZeroColumnPageToStable_eq_pageTwoCoordinate 1

local notation "B₀" =>
  (HomologicalComplex.zero : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (q : ℕ) : C :=
  HomologicalComplex₂.partialTotalZeroColumnStableSource (B := B₀) q

example (q : ℕ) :=
  HomologicalComplex₂.partialTotalZeroColumnPageTwoLeftIso (B := B₀) q

example (q : ℕ) :=
  HomologicalComplex₂.partialTotalZeroColumnStableTail (B := B₀) q

example (q : ℕ) :=
  HomologicalComplex₂.partialTotalZeroColumnPageToStable (B := B₀) q

example (q : ℕ) :=
  HomologicalComplex₂.partialTotalZeroColumnPageToStable_eq_pageTwoCoordinate
    (B := B₀) q

example (q : ℕ) :=
  HomologicalComplex₂.partialTotalZeroColumnEdge (B := B₀) q

/-! ## Filtration endpoints and exhaustion -/

example (n : ℕ) :
    IsZero ((B.partialTotalHomologyFiltration n).obj ⊥) :=
  B.isZero_partialTotalHomologyFiltration_obj_bot n

example (n : ℕ) :
    IsIso ((B.partialTotalHomologyFiltration n).ι.app ⊤) :=
  B.partialTotalHomologyFiltration_ι_app_top_isIso n

example (n : ℕ) :
    IsIso ((B.partialTotalHomologyFiltration n).ι.app
      (((n : ℕ) : ℤ) : EInt)) :=
  B.partialTotalHomologyFiltration_exhaustive_at_degree n

example (q : ℕ) :
    B.partialTotalZeroColumnEdge q =
      B.partialTotalZeroColumnPageToStable q ≫
        (B.partialTotalStableGradedIso q 0).hom ≫
        (B.partialTotalHomologyGradedZeroIso q).inv ≫
        (B.partialTotalHomologyFiltration q).ι.app ((0 : ℤ) : EInt) :=
  rfl

example (p : ℕ) :
    B.partialTotalTopRowEdge p =
      let f := (B.partialTotalHomologyFiltration p).ι.app
        (((p : ℕ) : ℤ) : EInt)
      let _ : IsIso f :=
        B.partialTotalHomologyFiltration_exhaustive_at_degree p
      inv f ≫ B.partialTotalHomologyFiltrationToStable p p ≫
        B.partialTotalTopRowStableToPage p := by
  rfl

/-! ## Zero-column collapse criterion -/

example (n : ℕ)
    (hIncoming : ∀ (r s : ℕ) (hr : 2 ≤ r), r + s = n + 1 →
      IsZero
        ((((B.partialTotalSpectralObject.spectralSequence core).page
          (r : ℤ) (by omega)).X (r, s)))) :
    IsIso (B.partialTotalZeroColumnPageToStable n) := by
  exact HomologicalComplex₂.isIso_partialTotalZeroColumnPageToStable_of_isZero_incoming
    B n hIncoming

example :
    IsIso (B.partialTotalZeroColumnPageToStable 0) := by
  exact HomologicalComplex₂.isIso_partialTotalZeroColumnPageToStable_of_isZero_incoming
    B 0 (by intro r s hr hrs; omega)

example
    (h20 : IsZero
      ((((B.partialTotalSpectralObject.spectralSequence core).page
        (2 : ℤ) (by omega)).X (2, 0)))) :
    IsIso (B.partialTotalZeroColumnPageToStable 1) := by
  apply HomologicalComplex₂.isIso_partialTotalZeroColumnPageToStable_of_isZero_incoming
    B 1
  intro r s hr hrs
  have hr' : r = 2 := by omega
  have hs' : s = 0 := by omega
  subst r
  subst s
  simpa using h20

/-! ## Chosen zero-column representative -/

example :
    B.X 0 ⟶ B.total (ComplexShape.down ℕ) :=
  B.partialTotalZeroRowToTotal

example (q : ℕ) :
    let χ := B.partialTotalFirstPageChoice
    (B.verticalHomologyComplex q).pOpcycles 0 ≫
        (B.verticalHomologyComplex q).isoHomologyι₀.inv ≫
        (χ.secondPageVerticalHomologyIso 0 q).inv ≫
        B.partialTotalZeroColumnEdge q =
      HomologicalComplex.homologyMap B.partialTotalZeroRowToTotal q :=
  B.partialTotalZeroColumnEdge_representation q

example :
    let χ := B.partialTotalFirstPageChoice
    (B.verticalHomologyComplex 0).pOpcycles 0 ≫
        (B.verticalHomologyComplex 0).isoHomologyι₀.inv ≫
        (χ.secondPageVerticalHomologyIso 0 0).inv ≫
        B.partialTotalZeroColumnEdge 0 =
      HomologicalComplex.homologyMap B.partialTotalZeroRowToTotal 0 :=
  B.partialTotalZeroColumnEdge_representation 0

example :
    let χ := B.partialTotalFirstPageChoice
    (B.verticalHomologyComplex 1).pOpcycles 0 ≫
        (B.verticalHomologyComplex 1).isoHomologyι₀.inv ≫
        (χ.secondPageVerticalHomologyIso 0 1).inv ≫
        B.partialTotalZeroColumnEdge 1 =
      HomologicalComplex.homologyMap B.partialTotalZeroRowToTotal 1 :=
  B.partialTotalZeroColumnEdge_representation 1

example :
    let Z := (HomologicalComplex.zero :
      HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ))
    Z.X 0 ⟶ HomologicalComplex₂.total Z (ComplexShape.down ℕ) :=
  HomologicalComplex₂.partialTotalZeroRowToTotal
    (B := (HomologicalComplex.zero :
      HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)))

example (q : ℕ) :
    let Z := (HomologicalComplex.zero :
      HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ))
    let χ := HomologicalComplex₂.partialTotalFirstPageChoice (B := Z)
    (HomologicalComplex₂.verticalHomologyComplex (B := Z) q).pOpcycles 0 ≫
        (HomologicalComplex₂.verticalHomologyComplex
          (B := Z) q).isoHomologyι₀.inv ≫
        (χ.secondPageVerticalHomologyIso 0 q).inv ≫
        HomologicalComplex₂.partialTotalZeroColumnEdge (B := Z) q =
      HomologicalComplex.homologyMap
        (HomologicalComplex₂.partialTotalZeroRowToTotal (B := Z)) q :=
  HomologicalComplex₂.partialTotalZeroColumnEdge_representation
    (B := (HomologicalComplex.zero :
      HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ))) q

end MathlibExtTest.Algebra.Homology.PartialTotalEdgeMaps

end
