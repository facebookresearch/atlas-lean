/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGRelativeCYDiagramLedger

/-!
# The actual compatible class and joint comparison in relative CY composition

The two input classes and the output class are computed from the signed
negative-cyclic compatibility fibre, the fixed coproduct isomorphisms,
and the full relative cone gluing map. The A/C exterior target and B
compatibility correction are retained. Boundary maps use the source
trace/duality evaluation and its shifted-unit normalization.

One projectively cofibrant module over the coherent grid tensored with
Z-bimodules supplies the joint comparison. Its naturality sees every
chain generator and every homogeneous coefficient action. Pointwise
homotopies identify its components with the actual class-induced maps;
they do not supply independent edge or square homotopies.

No class construction contains a nondegeneracy assertion.

Reference: Brav--Dyckerhoff, arXiv:1606.00619v1, Definition 4.11,
diagram 6.5 and Theorem 6.2 (including the completed diagrams 6.6--6.7).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGRelativeCYCospanGluing

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGMoritaClosedModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGModuleConeShiftModels
open MathlibExt.CategoryTheory.DGModuleUniversalConeModels
open MathlibExt.CategoryTheory.DGRelativeCalabiYauModels
open MathlibExt.CategoryTheory.DGRelativeCYDiagramLedger
open MathlibExt.CategoryTheory.DGMoritaCospanModels
open MathlibExt.CategoryTheory.DGCoherentIndexModels
open MathlibExt.CategoryTheory.DGCalabiYauMapModels
open MathlibExt.Algebra.Homology.DGCyclicMixedModels
open MathlibExt.Algebra.Homology.DGCategoryTraceModels
open MathlibExt.Algebra.Homology.RelativeCyclicGluing
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels

universe u
variable {k : Type u} [Field k]

theorem coefficientSquare (P : Cospan (k := k)) (S : NegativeTraceSystem k) :
    (S.map P.f).map ≫ (S.map P.i).map = (S.map P.g).map ≫ (S.map P.j).map := by
  rw [← S.map_comp, ← S.map_comp, P.square]

/-- Coefficient construction data contain only normalized cyclic coproduct and cone outputs. -/
structure CyclicData {P : Cospan (k := k)} {S : NegativeTraceSystem k} {n : ℤ}
    (D : ModuleData P S n) where
  left : NegativeCoproductModel S D.AB
  right : NegativeCoproductModel S D.BC
  outer : NegativeCoproductModel S D.AC
  gluing : CochainGluingModel (S.map P.e).map (S.map P.f).map (S.map P.g).map (S.map P.h).map
    (S.map P.i).map (S.map P.j).map (coefficientSquare P S)

namespace CyclicData

variable {P : Cospan (k := k)} {S : NegativeTraceSystem k} {n : ℤ}
  {D : ModuleData P S n} (T : CyclicData D)

def leftIso (T : CyclicData D) : relativeNegativeComplex S D.leftFunctor.functor ≅
    relativeX (S.map P.e).map (S.map P.f).map := by
  change CochainComplex.mappingCone (S.map D.leftFunctor.functor).map ≅
    CochainComplex.mappingCone (biprod.desc (S.map P.e).map (S.map P.f).map)
  have he : (S.map (D.AB.inl ≫ D.leftFunctor.functor)).map = (S.map P.e).map :=
    congrArg (fun f : P.A ⟶ P.X => (S.map f).map) D.leftFunctor.inl_eq
  have hf : (S.map (D.AB.inr ≫ D.leftFunctor.functor)).map = (S.map P.f).map :=
    congrArg (fun f : P.B ⟶ P.X => (S.map f).map) D.leftFunctor.inr_eq
  exact relativeCoefficientIso T.left D.leftFunctor.functor ≪≫
    eqToIso (congrArg (fun f : (S.negative P.A).complex ⊞ (S.negative P.B).complex ⟶ (S.negative P.X).complex =>
      CochainComplex.mappingCone f) (congrArg₂ biprod.desc he hf))

def rightIso (T : CyclicData D) : relativeNegativeComplex S D.rightFunctor.functor ≅
    relativeY (S.map P.g).map (S.map P.h).map := by
  change CochainComplex.mappingCone (S.map D.rightFunctor.functor).map ≅
    CochainComplex.mappingCone (biprod.desc (S.map P.g).map (S.map P.h).map)
  have hg : (S.map (D.BC.inl ≫ D.rightFunctor.functor)).map = (S.map P.g).map :=
    congrArg (fun f : P.B ⟶ P.Y => (S.map f).map) D.rightFunctor.inl_eq
  have hh : (S.map (D.BC.inr ≫ D.rightFunctor.functor)).map = (S.map P.h).map :=
    congrArg (fun f : P.C ⟶ P.Y => (S.map f).map) D.rightFunctor.inr_eq
  exact relativeCoefficientIso T.right D.rightFunctor.functor ≪≫
    eqToIso (congrArg (fun f : (S.negative P.B).complex ⊞ (S.negative P.C).complex ⟶ (S.negative P.Y).complex =>
      CochainComplex.mappingCone f) (congrArg₂ biprod.desc hg hh))

def outerIso (T : CyclicData D) : relativeNegativeComplex S D.outerFunctor.functor ≅
    compositeRelative (S.map P.e).map (S.map P.h).map (S.map P.i).map (S.map P.j).map := by
  change CochainComplex.mappingCone (S.map D.outerFunctor.functor).map ≅
    CochainComplex.mappingCone (biprod.desc ((S.map P.e).map ≫ (S.map P.i).map) ((S.map P.h).map ≫ (S.map P.j).map))
  have he : (S.map (D.AC.inl ≫ D.outerFunctor.functor)).map = (S.map P.e).map ≫ (S.map P.i).map :=
    (congrArg (fun f : P.A ⟶ P.Z => (S.map f).map) D.outerFunctor.inl_eq).trans (S.map_comp P.e P.i)
  have hh : (S.map (D.AC.inr ≫ D.outerFunctor.functor)).map = (S.map P.h).map ≫ (S.map P.j).map :=
    (congrArg (fun f : P.C ⟶ P.Z => (S.map f).map) D.outerFunctor.inr_eq).trans (S.map_comp P.h P.j)
  exact relativeCoefficientIso T.outer D.outerFunctor.functor ≪≫
    eqToIso (congrArg (fun f : (S.negative P.A).complex ⊞ (S.negative P.C).complex ⟶ (S.negative P.Z).complex =>
      CochainComplex.mappingCone f) (congrArg₂ biprod.desc he hh))

abbrev Compatible :=
  (𝟙_ (Cochains k))⟦n⟧ ⟶ sourceCompatibleComplex (S.map P.e).map (S.map P.f).map (S.map P.g).map (S.map P.h).map

def toSum (a : Compatible (P := P) (S := S) (n := n)) :
    CompatibleClass (S.map P.e).map (S.map P.f).map (S.map P.g).map (S.map P.h).map n :=
  a ≫ (sourceToCompatibleIso (S.map P.e).map (S.map P.f).map (S.map P.g).map (S.map P.h).map).hom

/-- The actual first projection is transported by the fixed coproduct-cone isomorphism. -/
def leftClass (T : CyclicData D) (a : Compatible (P := P) (S := S) (n := n)) :
    RelativeNegativeClass S D.leftFunctor.functor n :=
  a ≫ sourceProjectionX (S.map P.e).map (S.map P.f).map (S.map P.g).map (S.map P.h).map ≫ T.leftIso.inv

def rightClass (T : CyclicData D) (a : Compatible (P := P) (S := S) (n := n)) :
    RelativeNegativeClass S D.rightFunctor.functor n :=
  a ≫ sourceProjectionY (S.map P.e).map (S.map P.f).map (S.map P.g).map (S.map P.h).map ≫ T.rightIso.inv

/-- The output is the computed full relative gluing class, including exterior A and C. -/
def outerClass (a : Compatible (P := P) (S := S) (n := n)) :
    RelativeNegativeClass S D.outerFunctor.functor n := gluedClass T.gluing (toSum a) ≫ T.outerIso.inv

def boundaryAValue (a : Compatible (P := P) (S := S) (n := n))
    (v : ((𝟙_ (Cochains k))⟦n⟧).X (-n)) : (S.negative P.A).complex.X (1 - n) :=
  ((biprod.fst : (S.negative P.A).complex ⊞ (S.negative P.B).complex ⟶ (S.negative P.A).complex).f (1 - n))
    ((CochainComplex.mappingCone.fst (biprod.desc (S.map P.e).map (S.map P.f).map)).val.v
      (-n) (1 - n) (by omega)
      (((sourceProjectionX (S.map P.e).map (S.map P.f).map (S.map P.g).map (S.map P.h).map).f (-n))
        ((a.f (-n)) v)))

/-- The shared coefficient is -δ'_B on the X side, as in diagram 6.5. -/
def boundaryBValue (a : Compatible (P := P) (S := S) (n := n))
    (v : ((𝟙_ (Cochains k))⟦n⟧).X (-n)) : (S.negative P.B).complex.X (1 - n) :=
  -((biprod.snd : (S.negative P.A).complex ⊞ (S.negative P.B).complex ⟶ (S.negative P.B).complex).f
    (1 - n))
    ((CochainComplex.mappingCone.fst (biprod.desc (S.map P.e).map (S.map P.f).map)).val.v
      (-n) (1 - n) (by omega)
      (((sourceProjectionX (S.map P.e).map (S.map P.f).map (S.map P.g).map (S.map P.h).map).f (-n))
        ((a.f (-n)) v)))

/-- The C grid coefficient is the literal Y projection; the sum-cone conversion has already negated Y. -/
def boundaryCValue (a : Compatible (P := P) (S := S) (n := n))
    (v : ((𝟙_ (Cochains k))⟦n⟧).X (-n)) : (S.negative P.C).complex.X (1 - n) :=
  ((biprod.snd : (S.negative P.B).complex ⊞ (S.negative P.C).complex ⟶ (S.negative P.C).complex).f (1 - n))
    ((CochainComplex.mappingCone.fst (biprod.desc (S.map P.g).map (S.map P.h).map)).val.v
      (-n) (1 - n) (by omega)
      (((sourceProjectionY (S.map P.e).map (S.map P.f).map (S.map P.g).map (S.map P.h).map).f (-n))
        ((a.f (-n)) v)))

end CyclicData

/-- Source-to-sum conversion negates the Y class and every one of its actual module maps. -/
structure NegatedRelativeCYMaps {A B : DGCat k} {S : NegativeTraceSystem k} {n : ℤ}
    {DA : CYCategoryData S A} {DB : CYCategoryData S B} {f : A ⟶ B}
    {F : RelativeCYContext S f DA DB} {a : RelativeNegativeClass S f n} {C : RelativeConeContext F n}
    (M : RelativeCYMapModel F n a C) where
  negated : RelativeCYMapModel F n (-a) C
  boundary_eq : negated.boundary = -M.boundary
  nullhomotopy_eq : negated.nullhomotopy = -M.nullhomotopy
  middle_eq : negated.middle = negatedModuleMap M.middle
  left_eq : negated.left = negatedModuleMap M.left
  right_eq : negated.right = negatedModuleMap M.right

/-- A boundary class gives its literal evaluation cochain and map to the actual shift.
The construction carries no absolute CY or nondegeneracy assertion. -/
structure BoundaryModuleMap {S : NegativeTraceSystem k} {C : DGCat k}
    (D : CYCategoryData S C) (n : ℤ)
    (shift : CofibrantShiftModel (⟨D.bar.module, D.bar.cofibrant⟩) (1 - n))
    (coefficient : ((𝟙_ (Cochains k))⟦n⟧).X (-n) → (S.negative C).complex.X (1 - n)) where
  graded : DGHom k (1 - n) D.inverse.replacement.module D.bar.module
  closed : dgDifferential k (1 - n) graded = 0
  normalized : ∀ v : ((𝟙_ (Cochains k))⟦n⟧).X (-n),
    (D.evaluation.comparison.f (1 - n)) ((D.projection.map.f (1 - n)) (coefficient v)) =
      shiftedUnitScalar k n v • graded
  shifted : ShiftedModuleMapModel (1 - n) graded closed shift.toModuleShiftModel

/-- Actual input/output cone matrices and the three signed boundary maps. -/
structure CospanClassMaps {P : Cospan (k := k)} {S : NegativeTraceSystem k} {n : ℤ}
    {D : ModuleData P S n} (T : CyclicData D) (a : CyclicData.Compatible (P := P) (S := S) (n := n)) where
  left : RelativeCYMapModel D.left n (T.leftClass a) D.leftCone
  right : RelativeCYMapModel D.right n (T.rightClass a) D.rightCone
  rightNegation : NegatedRelativeCYMaps right
  outer : RelativeCYMapModel D.outer n (T.outerClass a) D.outerCone
  boundaryA : BoundaryModuleMap D.DA n D.shiftedA (CyclicData.boundaryAValue a)
  boundaryB : BoundaryModuleMap D.DB n D.shiftedB (CyclicData.boundaryBValue a)
  boundaryC : BoundaryModuleMap D.DC n D.shiftedC (CyclicData.boundaryCValue a)

/-- Every vertical is the actual induced class map, with all homogeneous signs retained. -/
def CospanClassMaps.vertical {P : Cospan (k := k)} {S : NegativeTraceSystem k} {n : ℤ}
    {D : ModuleData P S n} {T : CyclicData D}
    {a : CyclicData.Compatible (P := P) (S := S) (n := n)} (M : CospanClassMaps T a)
    (q : GridIndex) : (D.dualNode q.down).obj ⟶ (D.shiftedNode q.down).obj := by
  rcases q with ⟨r, c⟩
  refine Fin.cases ?_ (fun r => Fin.cases ?_ (fun r => Fin.cases ?_ (fun r => Fin.elim0 r) r) r) r
  all_goals refine Fin.cases ?_ (fun c => Fin.cases ?_ (fun c => Fin.cases ?_ (fun c => Fin.elim0 c) c) c) c
  all_goals dsimp [ModuleData.dualNode, ModuleData.shiftedNode]
  · exact M.outer.left
  · exact pushedModuleMap D.I.induction _ _ M.left.left
  · exact pushedModuleMap D.I.induction _ _ (pushedModuleMap D.E.induction _ _ M.boundaryA.shifted.map)
  · exact pushedModuleMap D.J.induction _ _ M.rightNegation.negated.left
  · exact pushedModuleMap D.M.induction _ _ M.boundaryB.shifted.map
  · exact pushedModuleMap D.I.induction _ _ M.left.right
  · exact pushedModuleMap D.J.induction _ _ (pushedModuleMap D.H.induction _ _ M.boundaryC.shifted.map)
  · exact pushedModuleMap D.J.induction _ _ M.rightNegation.negated.right
  · exact M.outer.right

/-- The one joint map has the actual relative CY maps as its normalized point components.
Its DG naturality supplies every edge/higher face over the common Z^e coefficients. -/
structure CospanClassComparison {P : Cospan (k := k)} {S : NegativeTraceSystem k} {n : ℤ}
    {D : ModuleData P S n} {O : CospanOperations D} (G : CompletedCospanDiagrams O)
    (T : CyclicData D) (a : CyclicData.Compatible (P := P) (S := S) (n := n)) where
  classes : CospanClassMaps T a
  joint : CurriedJointComparison G.index (enveloping P.Z P.Z) G.dual G.shifted
  pointHomotopy : ∀ q : GridIndex,
    DGHom k (-1) (joint.replacement.toEnrichedFunctor.obj (G.index.objects.symm q))
      (D.shiftedNode q.down).obj
  point_boundary : ∀ q : GridIndex, dgDifferential k (-1) (pointHomotopy q) =
    moduleCycle (columnMap joint.augmentation (G.index.objects.symm q) ≫
      eqToHom (G.dualObjects q) ≫ classes.vertical q) -
    moduleCycle (columnMap joint.map (G.index.objects.symm q) ≫ eqToHom (G.shiftedObjects q))

/-- A shared source integration chooses the whole normalized construction, never nondegeneracy.
It keeps the actual original bar/dual data and all compatible classes, not one selected CY class. -/
structure CospanTraceIntegration (P : Cospan (k := k)) (S : NegativeTraceSystem k) (n : ℤ)
    (DA : CYCategoryData S P.A) (DB : CYCategoryData S P.B) (DC : CYCategoryData S P.C)
    (DX : CYCategoryData S P.X) (DY : CYCategoryData S P.Y) (DZ : CYCategoryData S P.Z) where
  data : ModuleData P S n
  A_eq : data.DA = DA
  B_eq : data.DB = DB
  C_eq : data.DC = DC
  X_eq : data.DX = DX
  Y_eq : data.DY = DY
  Z_eq : data.DZ = DZ
  operations : CospanOperations data
  diagrams : CompletedCospanDiagrams operations
  coefficients : CyclicData data
  realize : ∀ a : CyclicData.Compatible (P := P) (S := S) (n := n),
    CospanClassComparison diagrams coefficients a

end MathlibExt.CategoryTheory.DGRelativeCYCospanGluing
