/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FormalNearbyCycleModels
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# All signed finite Tate coefficient reductions

The scalar map is the actual reduction Z/p^(r+1) → Z/p^r. Reduction of
roots is u ↦ u^p. Positive tensor words use native semilinear tensor maps;
negative words use the enriched internal Hom on every slice, normalized
by its evaluation against every local root section. The sheaf map is
fixed by the actual sheafification unit of every signed word.

The cochain carrier is the literal Milnor fiber of these finite
coefficient maps. It retains finite coefficients, torsion and signed Tate
conventions. Computing derived Rlim in a sheaf category additionally uses
resolved finite objects and derived products; the nearby comparison models
record that operation separately. Construction of the root/dual sheaf
reductions is separate from a syntomic or nearby-cycle comparison.

References: BMS19 arXiv:1802.03261v2, Theorem 10.1 and Remark 10.3;
BMS18 arXiv:1602.03148v3, Section 5.1; SGA4, Exposé IX.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FiniteTateCoefficientTowers

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Enriched.FunctorCategory
open CategoryTheory.MonoidalCategory
open scoped TensorProduct MonoidalClosed
open FiniteTateRootCoefficients

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) (r : ℕ)

/-- The source coefficient map on the actual finite rings. -/
def scalarReduction : Coeff p (r + 1) →+* Coeff p r where
  toFun x := ULift.up (ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ r)) (ZMod (p ^ r)) x.down)
  map_one' := by apply ULift.ext; exact map_one _
  map_mul' x y := by apply ULift.ext; exact map_mul _ _ _
  map_zero' := by apply ULift.ext; exact map_zero _
  map_add' x y := by apply ULift.ext; exact map_add _ _ _

variable {C : Type 1} [Category.{0} C] (O : Cᵒᵖ ⥤ CommRingCat.{0})
  (J : GrothendieckTopology C)

/-- A native coefficient-semilinear transformation, retaining every arrow. -/
structure SemiTransformation (M : Cᵒᵖ ⥤ ModuleCat.{1} (Coeff p (r + 1)))
    (N : Cᵒᵖ ⥤ ModuleCat.{1} (Coeff p r)) where
  app : ∀ U, M.obj U →ₛₗ[scalarReduction p r] N.obj U
  naturality : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.obj U),
    app V ((M.map f).hom x) = (N.map f).hom (app U x)

namespace SemiTransformation

variable {p r} {M : Cᵒᵖ ⥤ ModuleCat.{1} (Coeff p (r + 1))}
  {N : Cᵒᵖ ⥤ ModuleCat.{1} (Coeff p r)} (f : SemiTransformation p r M N)

set_option backward.isDefEq.respectTransparency false in
/-- Integer restriction preserves the source's actual semilinear map. -/
def integerMap : M ⋙ integerModules p (r + 1) ⟶ N ⋙ integerModules p r where
  app U := ModuleCat.ofHom
    (X := (integerModules p (r + 1)).obj (M.obj U))
    (Y := (integerModules p r).obj (N.obj U))
    { toFun := f.app U
      map_add' := map_add (f.app U)
      map_smul' a x := map_intCast_smul (f.app U).toAddMonoidHom
        (Coeff p (r + 1)) (Coeff p r) a x }
  naturality {U V} g := by
    apply ModuleCat.hom_ext
    ext x
    exact f.naturality g x

/-- Native tensor reduction on all pure tensors and all scalar coefficients. -/
def wordMap (g : SemiTransformation p r M N) (n : ℕ) (U : Cᵒᵖ) :
    (tensorWord p (r + 1) M n).obj U →ₛₗ[scalarReduction p r]
      (tensorWord p r N n).obj U :=
  match n with
  | 0 => show Coeff p (r + 1) →ₛₗ[scalarReduction p r] Coeff p r from
    { toFun := scalarReduction p r
      map_add' := map_add _
      map_smul' a b := map_mul _ a b }
  | n + 1 => TensorProduct.map (g.app U) (g.wordMap n U)

end SemiTransformation

/-- Evaluation of the actual enriched dual on every local slice object. -/
def dualValue (U : Cᵒᵖ) (V : Under U)
    (e : (dualPresheaf p r O J).obj U)
    (x : (rootSheaf p r O J).obj.obj V.right) :
    (constantUnit p r J).obj.obj V.right :=
  ((ihom.ev ((rootSheaf p r O J).obj.obj V.right)).app
    ((constantUnit p r J).obj.obj V.right)).hom
      (x ⊗ₜ (enrichedHomπ (ModuleCat.{1} (Coeff p r))
        (Under.forget U ⋙ (rootSheaf p r O J).obj)
        (Under.forget U ⋙ (constantUnit p r J).obj) V).hom e)

/-- Primitive construction output: root and unit maps are fixed on their
raw sections; the negative reduction preserves evaluation on every slice.
No dual functional is fixed by its value on the base object alone. -/
structure ReductionPrimitives where
  root : SemiTransformation p r (rootSheaf p (r + 1) O J).obj (rootSheaf p r O J).obj
  unit : SemiTransformation p r (constantUnit p (r + 1) J).obj (constantUnit p r J).obj
  dual : SemiTransformation p r (dualPresheaf p (r + 1) O J) (dualPresheaf p r O J)
  root_normalization :
    Functor.whiskerRight (toSheafify J (rootPresheaf p (r + 1) O))
      (integerModules p (r + 1)) ≫ root.integerMap =
    rootPowerPresheafMap p r O ≫
      Functor.whiskerRight (toSheafify J (rootPresheaf p r O)) (integerModules p r)
  unit_normalization : ∀ (U : Cᵒᵖ) (a : Coeff p (r + 1)),
    unit.app U ((toSheafify J (𝟙_ (Cᵒᵖ ⥤ ModuleCat.{1} (Coeff p (r + 1))))).app U a) =
      (toSheafify J (𝟙_ (Cᵒᵖ ⥤ ModuleCat.{1} (Coeff p r)))).app U (scalarReduction p r a)
  dual_normalization : ∀ (U : Cᵒᵖ) (V : Under U)
    (e : (dualPresheaf p (r + 1) O J).obj U)
    (x : (rootSheaf p (r + 1) O J).obj.obj V.right),
    dualValue p r O J U V (dual.app U e) (root.app V.right x) =
      unit.app V.right (dualValue p (r + 1) O J U V e x)

/-- Every signed sheaf arrow is construction output pinned to the native
tensor/dual reductions and to every actual sheafification unit. -/
structure SignedReduction where
  primitives : ReductionPrimitives p r O J
  word : ∀ i : ℤ, SemiTransformation p r (signedWord p (r + 1) O J i) (signedWord p r O J i)
  positive : ∀ (n : ℕ) (U : Cᵒᵖ),
    (word (Int.ofNat n)).app U = primitives.root.wordMap n U
  negative : ∀ (n : ℕ) (U : Cᵒᵖ),
    (word (Int.negSucc n)).app U = primitives.dual.wordMap (n + 1) U
  sheafMap : ∀ i : ℤ, integerTate p (r + 1) O J i ⟶ integerTate p r O J i
  sheaf_normalization : ∀ i : ℤ,
    Functor.whiskerRight (toSheafify J (signedWord p (r + 1) O J i))
      (integerModules p (r + 1)) ≫ (sheafMap i).hom =
    (word i).integerMap ≫
      Functor.whiskerRight (toSheafify J (signedWord p r O J i)) (integerModules p r)

/-- The coefficient tower has every positive finite level, starting at p. -/
structure TateTower where
  reduction : ∀ r : ℕ, SignedReduction p (r + 1) O J

namespace TateTower

variable {p O J} (T : TateTower p O J)

abbrev Sheaves (J : GrothendieckTopology C) := Sheaf J (ModuleCat.{1} ℤ)

instance countableSheafLimits : HasLimitsOfShape (Discrete ℕ) (Sheaves J) := by
  let : HasLimitsOfShape (Discrete ℕ) (ModuleCat.{1} ℤ) := ModuleCat.hasLimitsOfShape
  exact @Sheaf.instHasLimitsOfShape.{2, 1, 0, 1, 0, 0}
    C inferInstance J (ModuleCat.{1} ℤ) inferInstance (Discrete ℕ) inferInstance inferInstance

def finiteComplex (_T : TateTower p O J) (i : ℤ) (r : ℕ) : CochainComplex (Sheaves J) ℤ :=
  (HomologicalComplex.single (Sheaves J) (ComplexShape.up ℤ) 0).obj
    (integerTate p (r + 1) O J i)

def transition (i : ℤ) (r : ℕ) : T.finiteComplex i (r + 1) ⟶ T.finiteComplex i r :=
  (HomologicalComplex.single (Sheaves J) (ComplexShape.up ℤ) 0).map
    ((T.reduction r).sheafMap i)

def difference (i : ℤ) : ∏ᶜ (T.finiteComplex i) ⟶ ∏ᶜ (T.finiteComplex i) :=
  Pi.lift.{0, 1, 2} (fun r ↦ Pi.π.{0, 1, 2} (T.finiteComplex i) r -
    Pi.π.{0, 1, 2} (T.finiteComplex i) (r + 1) ≫ T.transition i r)

/-- Literal Milnor fiber of the source-normalized finite Tate cochains.
Derived Rlim requires the separately recorded resolved-product model. -/
def integralComplex (i : ℤ) : CochainComplex (Sheaves J) ℤ :=
  CochainComplex.mappingCocone (T.difference i)

def projection (i : ℤ) (r : ℕ) : T.integralComplex i ⟶ T.finiteComplex i r :=
  CochainComplex.mappingCocone.fst (T.difference i) ≫ Pi.π (T.finiteComplex i) r

def integral (i : ℤ) : DerivedCategory (Sheaves J) := DerivedCategory.Q.obj (T.integralComplex i)

end TateTower

end MathlibExt.AlgebraicGeometry.FiniteTateCoefficientTowers
