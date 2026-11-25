/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.TorusFixedSchemeModels
public import MathlibExt.AlgebraicGeometry.ComplexTorusTorsors
public import MathlibExt.AlgebraicGeometry.BundleTrace
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Actual characters and fixed/moving equivariant bundle summands

Characters are genuine algebraic group morphisms to G_m. Their
scalars are the pullback of the actual Laurent unit. Restriction
of a module linearization to a fixed scheme is computed through
the original comparison and native pullback-comp/congruence maps.

Weight summands have actual inclusion/projection module maps,
orthogonality and a complete direct-sum decomposition. Their
eigenvalue equations are equations of module maps on G×F, so
nonreduced parameters and all sections are retained. Fixed/moving
objects and their duals are the actual finite biproduct modules.

References: Graber–Pandharipande, arXiv:alg-geom/9708001v2,
§1; Maulik–Okounkov, arXiv:1211.1287v3, §3.3.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AlgebraicWeightBundleModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory _root_.CategoryTheory.MonObj _root_.Opposite
open _root_.AlgebraicGeometry
open IntegralChowChernModels CoherentCurveLinearSeries AlgebraicBundleGeometry
open LinearizedLineBundles TorusFixedSchemeModels

/-- Native finite products in the module sheaf category yield its finite biproducts. -/
instance schemeModulesFiniteBiproducts (Y : Scheme.{0}) : HasFiniteBiproducts Y.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

abbrev base : Scheme := Spec (.of ℂ)
abbrev Gm := ComplexTorusTorsors.Gm

/-- The actual Laurent unit defines the universal G_m coordinate. -/
def gmUnit : Γ(Gm.left, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (.of (LaurentPolynomial ℂ))).inv.hom.toMonoidHom
    (LaurentPolynomial.isUnit_T (R := ℂ) 1).unit

structure Character (G : Over base) [GrpObj G] where
  map : G ⟶ Gm
  [hom : IsMonHom map]

attribute [instance] Character.hom

def characterFunction {G : Over base} [GrpObj G] (chi : Character G) (F : Over base) :
    Γ((G ⊗ F).left, ⊤) :=
  (fst G F).left.appTop (chi.map.left.appTop (gmUnit : Γ(Gm.left, ⊤)))

/-- The inverse character appears in a*E to p*E, the inverse fibre transport. -/
def inverseCharacterFunction {G : Over base} [GrpObj G] (chi : Character G) (F : Over base) :
    Γ((G ⊗ F).left, ⊤) :=
  (fst G F).left.appTop (chi.map.left.appTop (gmUnit⁻¹ : Γ(Gm.left, ⊤)ˣ))

/-- On G_m the integer is pinned by its actual Laurent-coordinate ring map. -/
structure IntegerCharacter (chi : Character Gm) where
  weight : ℤ
  normalized : chi.map.left.appTop (gmUnit : Γ(Gm.left, ⊤)) =
    ((gmUnit ^ weight : Γ(Gm.left, ⊤)ˣ) : Γ(Gm.left, ⊤))

/-- Multiplication by the actual restricted regular function on every open. -/
def scalarEnd (Y : Scheme) (E : Y.Modules) (r : Γ(Y, ⊤)) : E ⟶ E where
  val.app U := by
    letI : CommRing (Y.ringCatSheaf.obj.obj U) :=
      inferInstanceAs (CommRing (Y.presheaf.obj U))
    let rU : Y.ringCatSheaf.obj.obj U :=
      (Y.presheaf.map (homOfLE (show U.unop≤⊤ from le_top)).op).hom r
    exact ModuleCat.ofHom
      { toFun := fun x => rU • x
        map_add' := by intro x y; exact smul_add rU x y
        map_smul' := by
          intro s x
          simp only [smul_smul]
          rw [mul_comm]
          rfl }
  val.naturality {U V} f := by
    apply ModuleCat.hom_ext
    ext x
    change ((Y.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op).hom r) •
        E.val.restrictₛₗ f x =
      E.val.restrictₛₗ f
        (((Y.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom r) • x)
    rw [(E.val.restrictₛₗ f).map_smulₛₗ]
    congr 1
    change _ = ((Y.presheaf.map f).hom.comp
      (Y.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom) r
    rw [← CommRingCat.hom_comp, ← Y.presheaf.map_comp]
    rfl

variable {G X F : Over base} [GrpObj G] [ModObj G X]

/-- The original linearization restricted to a genuinely fixed map. -/
def fixedComparison {E : X.left.Modules} (A : Linearization G X E)
    (i : F ⟶ X) (hi : FixedPoint G X i) :
    (Scheme.Modules.pullback (snd G F).left).obj ((Scheme.Modules.pullback i.left).obj E) ≅
      (Scheme.Modules.pullback (snd G F).left).obj ((Scheme.Modules.pullback i.left).obj E) :=
  (Scheme.Modules.pullbackComp (snd G F).left i.left).app E ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hi).symm).app E ≪≫
    ((Scheme.Modules.pullbackComp (G ◁ i).left (action G X)).app E).symm ≪≫
    (Scheme.Modules.pullback (G ◁ i).left).mapIso A.comparison ≪≫
    (Scheme.Modules.pullbackComp (G ◁ i).left (projection G X)).app E ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (whiskerLeft_snd G i))).app E ≪≫
    ((Scheme.Modules.pullbackComp (snd G F).left i.left).app E).symm

/-- Equivariance of the actual original bundle/module differential. -/
def IsLinearizedMap {E K : X.left.Modules} (A : Linearization G X E)
    (B : Linearization G X K) (d : E ⟶ K) : Prop :=
  (Scheme.Modules.pullback (action G X)).map d ≫ B.comparison.hom =
    A.comparison.hom ≫ (Scheme.Modules.pullback (projection G X)).map d

/-- Every summand is an actual submodule with its genuine algebraic character action. -/
structure WeightDecomposition {E : X.left.Modules} (A : Linearization G X E)
    (i : F ⟶ X) (hi : FixedPoint G X i) where
  count : ℕ
  character : Fin count → Character G
  bundle : Fin count → F.left.Modules
  rank : Fin count → ℕ
  locallyFree : ∀ j, IsBundle (bundle j) (rank j)
  inclusion : ∀ j, bundle j ⟶ (Scheme.Modules.pullback i.left).obj E
  projection : ∀ j, (Scheme.Modules.pullback i.left).obj E ⟶ bundle j
  retract : ∀ j, inclusion j ≫ projection j=𝟙 (bundle j)
  orthogonal : ∀ j k, j≠k → inclusion j ≫ projection k=0
  complete : ∑ j, projection j ≫ inclusion j=𝟙 _
  eigen : ∀ j,
    (Scheme.Modules.pullback (snd G F).left).map (inclusion j) ≫ (fixedComparison A i hi).hom =
      scalarEnd (G ⊗ F).left ((Scheme.Modules.pullback (snd G F).left).obj (bundle j))
        (inverseCharacterFunction (character j) F) ≫
          (Scheme.Modules.pullback (snd G F).left).map (inclusion j)

def IsTrivialCharacter {G : Over base} [GrpObj G] (chi : Character G) : Prop :=
  chi.map=toUnit G ≫ η[Gm]

def WeightDecomposition.fixed {E : X.left.Modules} {A : Linearization G X E}
    {i : F ⟶ X} {hi : FixedPoint G X i} (D : WeightDecomposition A i hi) : F.left.Modules := by
  classical
  letI := Fintype.ofFinite {j : Fin D.count // IsTrivialCharacter (D.character j)}
  exact biproduct (fun j : {j : Fin D.count // IsTrivialCharacter (D.character j)} => D.bundle
    j.val)

def WeightDecomposition.moving {E : X.left.Modules} {A : Linearization G X E}
    {i : F ⟶ X} {hi : FixedPoint G X i} (D : WeightDecomposition A i hi) : F.left.Modules := by
  classical
  letI := Fintype.ofFinite {j : Fin D.count // ¬IsTrivialCharacter (D.character j)}
  exact biproduct (fun j : {j : Fin D.count // ¬IsTrivialCharacter (D.character j)} => D.bundle
    j.val)

def WeightDecomposition.movingDual {E : X.left.Modules} {A : Linearization G X E}
    {i : F ⟶ X} {hi : FixedPoint G X i} (D : WeightDecomposition A i hi) : F.left.Modules :=
  BundleTrace.homSheaf F.left D.moving (structureModule F.left)

/-- Inclusion of all genuine weight-zero summands into the original restricted module. -/
def WeightDecomposition.fixedInclusion {E : X.left.Modules} {A : Linearization G X E}
    {i : F ⟶ X} {hi : FixedPoint G X i} (D : WeightDecomposition A i hi) :
    D.fixed ⟶ (Scheme.Modules.pullback i.left).obj E := by
  classical
  letI := Fintype.ofFinite {j : Fin D.count // IsTrivialCharacter (D.character j)}
  exact biproduct.desc (fun j : {j : Fin D.count // IsTrivialCharacter (D.character j)} =>
    D.inclusion j.val)

/-- Projection to all genuine weight-zero summands. -/
def WeightDecomposition.fixedProjection {E : X.left.Modules} {A : Linearization G X E}
    {i : F ⟶ X} {hi : FixedPoint G X i} (D : WeightDecomposition A i hi) :
    (Scheme.Modules.pullback i.left).obj E ⟶ D.fixed := by
  classical
  letI := Fintype.ofFinite {j : Fin D.count // IsTrivialCharacter (D.character j)}
  exact biproduct.lift (fun j : {j : Fin D.count // IsTrivialCharacter (D.character j)} =>
    D.projection j.val)

/-- Inclusion of all nonzero-weight summands. -/
def WeightDecomposition.movingInclusion {E : X.left.Modules} {A : Linearization G X E}
    {i : F ⟶ X} {hi : FixedPoint G X i} (D : WeightDecomposition A i hi) :
    D.moving ⟶ (Scheme.Modules.pullback i.left).obj E := by
  classical
  letI := Fintype.ofFinite {j : Fin D.count // ¬IsTrivialCharacter (D.character j)}
  exact biproduct.desc (fun j : {j : Fin D.count // ¬IsTrivialCharacter (D.character j)} =>
    D.inclusion j.val)

/-- Projection to all nonzero-weight summands. -/
def WeightDecomposition.movingProjection {E : X.left.Modules} {A : Linearization G X E}
    {i : F ⟶ X} {hi : FixedPoint G X i} (D : WeightDecomposition A i hi) :
    (Scheme.Modules.pullback i.left).obj E ⟶ D.moving := by
  classical
  letI := Fintype.ofFinite {j : Fin D.count // ¬IsTrivialCharacter (D.character j)}
  exact biproduct.lift (fun j : {j : Fin D.count // ¬IsTrivialCharacter (D.character j)} =>
    D.projection j.val)

/-- The fixed differential is the native restricted map between the genuine summands. -/
def fixedDifferential {E K : X.left.Modules} {A : Linearization G X E}
    {B : Linearization G X K} {i : F ⟶ X} {hi : FixedPoint G X i}
    (D : WeightDecomposition A i hi) (Q : WeightDecomposition B i hi) (d : E ⟶ K) :
    D.fixed ⟶ Q.fixed :=
  D.fixedInclusion ≫ (Scheme.Modules.pullback i.left).map d ≫ Q.fixedProjection

/-- The moving differential is the same actual restriction to its nonzero weights. -/
def movingDifferential {E K : X.left.Modules} {A : Linearization G X E}
    {B : Linearization G X K} {i : F ⟶ X} {hi : FixedPoint G X i}
    (D : WeightDecomposition A i hi) (Q : WeightDecomposition B i hi) (d : E ⟶ K) :
    D.moving ⟶ Q.moving :=
  D.movingInclusion ≫ (Scheme.Modules.pullback i.left).map d ≫ Q.movingProjection

/-- On the affine line, the native pullback cotangent differential has scalar c.
Thus its geometric cotangent character is minus one, and its dual normal
character is plus one. The equality holds over every coefficient ring. -/
theorem weightOneCoordinateDifferential (A : Type) [CommRing A] (c : A) :
    KaehlerDifferential.D A (Polynomial A) (Polynomial.C c * Polynomial.X) =
      c • KaehlerDifferential.D A (Polynomial A) Polynomial.X := by
  have hp : Polynomial.C c * Polynomial.X = c • (Polynomial.X : Polynomial A) := by
    simp [Algebra.smul_def]
  rw [hp]
  exact (KaehlerDifferential.D A (Polynomial A)).toLinearMap.map_smul c Polynomial.X

end MathlibExt.AlgebraicGeometry.AlgebraicWeightBundleModels
