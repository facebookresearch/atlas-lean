/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Zero
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory

/-!
# Native functorial replacements from the original cardinal data

Use the original I factorization on the full zero-to-object Arrow functor and
the original J factorization on the full object-to-zero Arrow functor. The
same κ, caller bottom, intermediate functors and natural maps are retained.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.Replacement

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

attribute [local instance] Native.modelCategory

/-- Original same-κ free-I replacement on the actual full enriched diagrams. -/
def cofibrantReplacement : EnrichedFunctorCat PointedCGWH.{u, v} A ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} A :=
  Diagrams.fromZeroArrow ⋙ (Native.cofibrantFactorizationData (B := B) (A := A)).Z

/-- Original same-κ free-J replacement into the same actual original zero diagram. -/
def fibrantReplacement : EnrichedFunctorCat PointedCGWH.{u, v} A ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} A :=
  Diagrams.toZeroArrow ⋙ (Native.fibrantFactorizationData (B := B) (A := A)).Z

/-- The entire original first I arrow, natural in the original diagram. -/
def initialToCofibrantReplacement :
    (Functor.const (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj Diagrams.zeroDiagram ⟶
      cofibrantReplacement (A := A) :=
  Functor.whiskerLeft Diagrams.fromZeroArrow
    (Native.cofibrantFactorizationData (B := B) (A := A)).i

/-- The entire original second I arrow is the natural trivial fibration to the identity. -/
def cofibrantReplacementCounit :
    cofibrantReplacement (A := A) ⟶ 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  Functor.whiskerLeft Diagrams.fromZeroArrow
    (Native.cofibrantFactorizationData (B := B) (A := A)).p

/-- The entire original first J arrow is the natural trivial cofibration from the identity. -/
def fibrantReplacementUnit :
    𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} A) ⟶ fibrantReplacement (A := A) :=
  Functor.whiskerLeft Diagrams.toZeroArrow
    (Native.fibrantFactorizationData (B := B) (A := A)).i

/-- The entire original second J arrow is the natural fibration to the same zero diagram. -/
def fibrantReplacementToZero :
    fibrantReplacement (A := A) ⟶
      (Functor.const (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj Diagrams.zeroDiagram :=
  Functor.whiskerLeft Diagrams.toZeroArrow
    (Native.fibrantFactorizationData (B := B) (A := A)).p

theorem cofibrantReplacementCounit_naturality
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    cofibrantReplacement.map f ≫ cofibrantReplacementCounit.app Y =
      cofibrantReplacementCounit.app X ≫ f :=
  cofibrantReplacementCounit.naturality f

theorem fibrantReplacementUnit_naturality
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    f ≫ fibrantReplacementUnit.app Y =
      fibrantReplacementUnit.app X ≫ fibrantReplacement.map f :=
  fibrantReplacementUnit.naturality f

theorem initialToCofibrantReplacement_naturality
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    initialToCofibrantReplacement.app X ≫ cofibrantReplacement.map f =
      initialToCofibrantReplacement.app Y := by
  calc
    initialToCofibrantReplacement.app X ≫ cofibrantReplacement.map f =
        𝟙 (Diagrams.zeroDiagram (A := A)) ≫ initialToCofibrantReplacement.app Y :=
      (initialToCofibrantReplacement.naturality f).symm
    _ = initialToCofibrantReplacement.app Y := Category.id_comp _

theorem fibrantReplacementToZero_naturality
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    fibrantReplacement.map f ≫ fibrantReplacementToZero.app Y =
      fibrantReplacementToZero.app X := by
  calc
    fibrantReplacement.map f ≫ fibrantReplacementToZero.app Y =
        fibrantReplacementToZero.app X ≫ 𝟙 (Diagrams.zeroDiagram (A := A)) :=
      fibrantReplacementToZero.naturality f
    _ = fibrantReplacementToZero.app X := Category.comp_id _

/-- The same original I natural arrows factor the caller's actual zero-to-object map. -/
theorem cofibrantReplacement_fac (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    initialToCofibrantReplacement.app X ≫ cofibrantReplacementCounit.app X =
      Diagrams.zeroTo X :=
  (Native.cofibrantFactorizationData (B := B) (A := A)).fac_app

/-- The same original J natural arrows factor the caller's actual object-to-zero map. -/
theorem fibrantReplacement_fac (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrantReplacementUnit.app X ≫ fibrantReplacementToZero.app X =
      Diagrams.toZero X :=
  (Native.fibrantFactorizationData (B := B) (A := A)).fac_app

theorem initialToCofibrantReplacement_mem_cofibrations
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
      (initialToCofibrantReplacement.app X) :=
  (Native.cofibrantFactorizationData (B := B) (A := A)).hi _

theorem cofibrantReplacementCounit_mem_trivialFibrations
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
      (cofibrantReplacementCounit.app X) :=
  (Native.cofibrantFactorizationData (B := B) (A := A)).hp _

theorem cofibrantReplacementCounit_mem_fibrations
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
      (cofibrantReplacementCounit.app X) :=
  (cofibrantReplacementCounit_mem_trivialFibrations X).1

theorem cofibrantReplacementCounit_mem_weakEquivalences
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)
      (cofibrantReplacementCounit.app X) :=
  (cofibrantReplacementCounit_mem_trivialFibrations X).2

theorem fibrantReplacementUnit_mem_trivialCofibrations
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
      (fibrantReplacementUnit.app X) :=
  (Native.fibrantFactorizationData (B := B) (A := A)).hi _

theorem fibrantReplacementUnit_mem_cofibrations
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
      (fibrantReplacementUnit.app X) :=
  (fibrantReplacementUnit_mem_trivialCofibrations X).1

theorem fibrantReplacementUnit_mem_weakEquivalences
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)
      (fibrantReplacementUnit.app X) :=
  (fibrantReplacementUnit_mem_trivialCofibrations X).2

theorem fibrantReplacementToZero_mem_fibrations
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
      (fibrantReplacementToZero.app X) :=
  (Native.fibrantFactorizationData (B := B) (A := A)).hp _

theorem isCofibrant_cofibrantReplacement
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    IsCofibrant (cofibrantReplacement.obj X) := by
  rw [isCofibrant_iff_of_isInitial (initialToCofibrantReplacement.app X)
    Diagrams.zeroDiagramIsInitial]
  exact (cofibration_iff _).2 (initialToCofibrantReplacement_mem_cofibrations X)

theorem isFibrant_fibrantReplacement
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    IsFibrant (fibrantReplacement.obj X) := by
  rw [isFibrant_iff_of_isTerminal (fibrantReplacementToZero.app X)
    Diagrams.zeroDiagramIsTerminal]
  exact (fibration_iff _).2 (fibrantReplacementToZero_mem_fibrations X)

theorem cofibrantReplacement_map_mem_weakEquivalences
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) f) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) (cofibrantReplacement.map f) := by
  apply (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).of_postcomp
    (cofibrantReplacement.map f) (cofibrantReplacementCounit.app Y)
    (cofibrantReplacementCounit_mem_weakEquivalences Y)
  rw [cofibrantReplacementCounit_naturality]
  exact (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).comp_mem _ _
    (cofibrantReplacementCounit_mem_weakEquivalences X) hf

theorem fibrantReplacement_map_mem_weakEquivalences
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) f) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) (fibrantReplacement.map f) := by
  apply (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).of_precomp
    (fibrantReplacementUnit.app X) (fibrantReplacement.map f)
    (fibrantReplacementUnit_mem_weakEquivalences X)
  rw [← fibrantReplacementUnit_naturality]
  exact (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).comp_mem _ _ hf
    (fibrantReplacementUnit_mem_weakEquivalences Y)

/-- The whole cofibrant replacement functor is the original same-κ I middle functor. -/
theorem cofibrantReplacement_eq_original :
    letI : (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u,
      v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := Native.generatorsI_isCardinalForSmallObjectArgument
    cofibrantReplacement (A := A) = Diagrams.fromZeroArrow ⋙
      (SmallObject.functorialFactorizationData
        (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v})
        realizedGeneratorCardinal.{v}).Z := rfl

/-- The whole fibrant replacement functor is the original same-κ J middle functor. -/
theorem fibrantReplacement_eq_original :
    letI : (generators (A := A) PointedCGWH.realizedHornInclusions.{u,
      v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := Native.generatorsJ_isCardinalForSmallObjectArgument
    fibrantReplacement (A := A) = Diagrams.toZeroArrow ⋙
      (SmallObject.functorialFactorizationData
        (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v})
        realizedGeneratorCardinal.{v}).Z := rfl

/-- The complete original I first natural arrow is retained. -/
theorem initialToCofibrantReplacement_eq_original :
    letI : (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u,
      v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := Native.generatorsI_isCardinalForSmallObjectArgument
    initialToCofibrantReplacement (A := A) =
      Functor.whiskerLeft Diagrams.fromZeroArrow
        (SmallObject.functorialFactorizationData
          (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v})
          realizedGeneratorCardinal.{v}).i := rfl

/-- The complete original I second natural arrow is retained. -/
theorem cofibrantReplacementCounit_eq_original :
    letI : (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u,
      v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := Native.generatorsI_isCardinalForSmallObjectArgument
    cofibrantReplacementCounit (A := A) =
      Functor.whiskerLeft Diagrams.fromZeroArrow
        (SmallObject.functorialFactorizationData
          (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v})
          realizedGeneratorCardinal.{v}).p := rfl

/-- The complete original J first natural arrow is retained. -/
theorem fibrantReplacementUnit_eq_original :
    letI : (generators (A := A) PointedCGWH.realizedHornInclusions.{u,
      v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := Native.generatorsJ_isCardinalForSmallObjectArgument
    fibrantReplacementUnit (A := A) =
      Functor.whiskerLeft Diagrams.toZeroArrow
        (SmallObject.functorialFactorizationData
          (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v})
          realizedGeneratorCardinal.{v}).i := rfl

/-- The complete original J second natural arrow is retained. -/
theorem fibrantReplacementToZero_eq_original :
    letI : (generators (A := A) PointedCGWH.realizedHornInclusions.{u,
      v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := Native.generatorsJ_isCardinalForSmallObjectArgument
    fibrantReplacementToZero (A := A) =
      Functor.whiskerLeft Diagrams.toZeroArrow
        (SmallObject.functorialFactorizationData
          (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v})
          realizedGeneratorCardinal.{v}).p := rfl

/-- Every Q map is the full original I intermediate map of the caller's square. -/
theorem cofibrantReplacement_map_eq_original
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    letI : (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u,
      v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := Native.generatorsI_isCardinalForSmallObjectArgument
    cofibrantReplacement.map f =
      SmallObject.objMap (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v})
        realizedGeneratorCardinal.{v} (Diagrams.fromZeroArrow.map f) := rfl

/-- Every R map is the full original J intermediate map of the caller's square. -/
theorem fibrantReplacement_map_eq_original
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    letI : (generators (A := A) PointedCGWH.realizedHornInclusions.{u,
      v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := Native.generatorsJ_isCardinalForSmallObjectArgument
    fibrantReplacement.map f =
      SmallObject.objMap (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v})
        realizedGeneratorCardinal.{v} (Diagrams.toZeroArrow.map f) := rfl

/-- The actual original Q comparison is inverted by the actual level projection. -/
theorem isIso_toHomotopyCategory_cofibrantReplacementCounit
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    IsIso ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
      (cofibrantReplacementCounit.app X)) :=
  Localization.inverts (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (cofibrantReplacementCounit.app X) (cofibrantReplacementCounit_mem_weakEquivalences X)

/-- The actual original R comparison is inverted by the actual level projection. -/
theorem isIso_toHomotopyCategory_fibrantReplacementUnit
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    IsIso ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
      (fibrantReplacementUnit.app X)) :=
  Localization.inverts (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (fibrantReplacementUnit.app X) (fibrantReplacementUnit_mem_weakEquivalences X)

/-- Full natural compatibility of Q with the actual level homotopy projection. -/
def cofibrantReplacementProjectionIso :
    cofibrantReplacement (A := A) ⋙
      toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ≅
    toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := by
  let α := Functor.whiskerRight (cofibrantReplacementCounit (A := A))
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
  let _ : ∀ X, IsIso (α.app X) := isIso_toHomotopyCategory_cofibrantReplacementCounit
  let _ : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- Full natural compatibility of R with the actual level homotopy projection. -/
def fibrantReplacementProjectionIso :
    toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ≅
    fibrantReplacement (A := A) ⋙
      toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := by
  let α := Functor.whiskerRight (fibrantReplacementUnit (A := A))
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
  let _ : ∀ X, IsIso (α.app X) := isIso_toHomotopyCategory_fibrantReplacementUnit
  let _ : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

theorem cofibrantReplacementProjectionIso_hom_app
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (cofibrantReplacementProjectionIso (A := A)).hom.app X =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        (cofibrantReplacementCounit.app X) := rfl

theorem fibrantReplacementProjectionIso_hom_app
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (fibrantReplacementProjectionIso (A := A)).hom.app X =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        (fibrantReplacementUnit.app X) := rfl

end HomotopicalAlgebra.EnrichedProjective.Native.Replacement

/-!
## Cones from the same original I factorization

Apply the original I middle functor to the unchanged object-to-zero arrows.
The two full natural factors supply the cofibration inclusion and trivial-fibration
contraction, with the same cardinal and caller bottom.
-/

namespace HomotopicalAlgebra.EnrichedProjective.Native.OriginalICone

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

attribute [local instance] Native.modelCategory

/-- The original I middle functor applied to the actual object-to-zero arrows. -/
def cone : EnrichedFunctorCat PointedCGWH.{u, v} I ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} I :=
  Diagrams.toZeroArrow ⋙ (Native.cofibrantFactorizationData (B := B) (A := I)).Z

/-- The original I first-factor natural transformation. -/
def inclusion : 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I) ⟶ cone (B := B) :=
  Functor.whiskerLeft Diagrams.toZeroArrow
    (Native.cofibrantFactorizationData (B := B) (A := I)).i

/-- The original I second factor, into the unchanged actual zero diagram. -/
def contraction : cone (B := B) ⟶
    (Functor.const (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Diagrams.zeroDiagram :=
  Functor.whiskerLeft Diagrams.toZeroArrow
    (Native.cofibrantFactorizationData (B := B) (A := I)).p

theorem inclusion_cofibration (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) ((inclusion (B := B)).app X) :=
  (Native.cofibrantFactorizationData (B := B) (A := I)).hi _

theorem contraction_trivialFibration (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)
      ((contraction (B := B)).app X) :=
  (Native.cofibrantFactorizationData (B := B) (A := I)).hp _

theorem contraction_eq_toZero (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (contraction (B := B)).app X = Diagrams.toZero ((cone (B := B)).obj X) :=
  Diagrams.zeroDiagramIsTerminal.hom_ext _ _

theorem inclusion_contraction (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (inclusion (B := B)).app X ≫ (contraction (B := B)).app X = Diagrams.toZero X :=
  (Native.cofibrantFactorizationData (B := B) (A := I)).fac_app

theorem cone_isCofibrant (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X] :
    IsCofibrant ((cone (B := B)).obj X) := by
  let _ : Cofibration ((inclusion (B := B)).app X) :=
    (cofibration_iff _).mpr (inclusion_cofibration X)
  exact isCofibrant_of_cofibration (X := X) ((inclusion (B := B)).app X)

theorem cone_map {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    (cone (B := B)).map f =
      (Native.cofibrantFactorizationData (B := B) (A := I)).Z.map
        (Diagrams.toZeroArrow.map f) := rfl

/-- Reuse the canonical Arrow functor on the actual original Q and counit. -/
def replacementArrowCounit :
    (Replacement.cofibrantReplacement (B := B) (A := I)).mapArrow ⟶
      (𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I)).mapArrow :=
  (Functor.mapArrowFunctor _ _).map (Replacement.cofibrantReplacementCounit (B := B))

theorem replacementArrowCounit_left (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    ((replacementArrowCounit (B := B)).app F).left =
      Replacement.cofibrantReplacementCounit.app F.left := rfl

theorem replacementArrowCounit_right (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    ((replacementArrowCounit (B := B)).app F).right =
      Replacement.cofibrantReplacementCounit.app F.right := rfl

theorem replacementArrowCounit_square (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    Replacement.cofibrantReplacement.map F.hom ≫
        ((replacementArrowCounit (B := B)).app F).right =
      ((replacementArrowCounit (B := B)).app F).left ≫ F.hom :=
  Replacement.cofibrantReplacementCounit_naturality F.hom

end HomotopicalAlgebra.EnrichedProjective.Native.OriginalICone
