/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.ProperShufflePolynomialColumns
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentHomology
public import MathlibExt.AlgebraicTopology.DoldKan.AdditiveNormalization
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Coefficient cotangent targets and André–Quillen chain models

Let `k` be a commutative `ℚ`-algebra, `B` a commutative `k`-algebra, and `M` a compatible
`B`-module in an independent carrier universe. For `P → B`, scalar-tower cancellation
identifies `M ⊗[B] (B ⊗[P] Ω[P/k])` with `M ⊗[P] Ω[P/k]`. On a differential tensor the map
sends `m ⊗ (b ⊗ dp)` to `(b • m) ⊗ dp`, retaining the specified carrier lift in the
coefficient cotangent target.

The comparison is natural in algebra maps over `B` and identifies their simplicial coefficient
cotangent diagrams. For the polynomial resolution of `B`, additive normalization identifies
this diagram with the ground restriction of `M ⊗[B] L_{B/k}`. The Dold–Kan comparison gives a
homotopy equivalence with its alternating-face complex, and scalar restriction identifies its
homology with the ground module underlying André–Quillen homology.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.AugmentedAlgebra

variable (k : Type u) [CommRing k] [Algebra ℚ k] (B : CommAlgCat.{max u v} k)
  (M : Type w) [AddCommGroup M] [Module k M] [Module B M]
  [SMulCommClass k B M] [IsScalarTower k B M]

attribute [local instance] coefficientModule coefficientCommutes coefficientTower scalarAugmentation_epi
attribute [local instance_reducible] CommAlgCat.cotangentAlgebra CommAlgCat.cotangentScalarTower
attribute [local instance] CommAlgCat.cotangentAlgebra CommAlgCat.cotangentScalarTower

/-- The scalar tower of a coefficient module along an augmentation.

For `P → B`, the action on `M` restricted through the augmentation gives `IsScalarTower P B
M`. -/
local instance coefficientThroughTarget (P : Over B) : IsScalarTower P.left B M :=
  IsScalarTower.of_compHom P.left B M

/-- Commutation of source and target coefficient actions.

For `P → B`, the induced `P`-action on the `B`-module `M` commutes with the `B`-action. -/
local instance coefficientSourceTargetCommutes (P : Over B) : SMulCommClass P.left B M where
  smul_comm p b m := by
    change P.hom.hom p • (b • m) = b • (P.hom.hom p • m)
    exact smul_comm (P.hom.hom p) b m

/-- The left-coefficient tensor functor on cotangent modules.

For `P → B`, this is the `B`-module `M ⊗[B] (B ⊗[P] Ω[P/k])`, with `M` in the left tensor
factor. -/
def nativeCoefficientFunctor : Over B ⥤ ModuleCat.{max u v w} B :=
  CommAlgCat.cotangentFunctor k B ⋙
    (ModuleCat.tensorBifunctorAt.{max u v, w, max u v} B).obj (ModuleCat.of B M)

/-- The ground restriction of the coefficient cotangent functor.

Apply the left-coefficient tensor functor over `B` and restrict its scalar action along `k →
B`. -/
def nativeGroundCoefficientFunctor : Over B ⥤ ModuleCat.{max u v w} k :=
  nativeCoefficientFunctor k B M ⋙ ModuleCat.restrictScalars (algebraMap k B)

/-- The coefficient scalar-tower cancellation for cotangent modules.

For `P → B`, the ground-linear equivalence `M ⊗[B] (B ⊗[P] Ω[P/k]) ≃ₗ[k] M ⊗[P] Ω[P/k]`
multiplies the middle scalar into the coefficient. -/
def coefficientTensorCancellation (P : Over B) :
    M ⊗[B] (B ⊗[P.left] KaehlerDifferential k P.left) ≃ₗ[k]
      M ⊗[P.left] KaehlerDifferential k P.left :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange P.left B B M (KaehlerDifferential k P.left)).restrictScalars k

/-- The tensor coordinates of ground-restricted coefficient cotangents.

The ground-restricted coefficient cotangent object is linearly equivalent to the same tensor
carrier `M ⊗[B] (B ⊗[P] Ω[P/k])`, with its given compatible ground action. -/
def nativeCoefficientRestrictionEquiv (P : Over B) :
    (nativeGroundCoefficientFunctor k B M).obj P ≃ₗ[k]
      M ⊗[B] (B ⊗[P.left] KaehlerDifferential k P.left) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' r x := by
    let T := M ⊗[B] (B ⊗[P.left] KaehlerDifferential k P.left)
    let y : T := x
    change (algebraMap k B r) • y = (RingHom.id k r) • y
    exact IsScalarTower.algebraMap_smul B r y

/-- The comparison with the lifted coefficient cotangent target.

Scalar restriction, tensor cancellation, and the coefficient carrier lift identify the ground
coefficient tensor object with the cotangent target `ULift.{u}(M ⊗[P] Ω[P/k])`. -/
def nativeCoefficientLevelIso (P : Over B) :
    (nativeGroundCoefficientFunctor k B M).obj P ≅ cotangentModule k B M P :=
  ((nativeCoefficientRestrictionEquiv k B M P).trans
    ((coefficientTensorCancellation k B M P).trans
      (ULift.moduleEquiv : ULift.{u} (M ⊗[P.left] KaehlerDifferential k P.left) ≃ₗ[k]
        M ⊗[P.left] KaehlerDifferential k P.left).symm)).toModuleIso

omit [Algebra ℚ k] [SMulCommClass k B M] in
/-- The differential-tensor value of the coefficient cotangent comparison.

The comparison sends `m ⊗ (b ⊗ dp)` to `up((b • m) ⊗ dp)`. This coordinate formula is stated
without a rational scalar assumption. -/
theorem nativeCoefficientLevelIso_tmul_D (P : Over B) (m : M) (b : B) (p : P.left) :
    (nativeCoefficientLevelIso k B M P).hom.hom
      (m ⊗ₜ[B] (b ⊗ₜ[P.left] KaehlerDifferential.D k P.left p)) =
        ULift.up ((b • m) ⊗ₜ[P.left] KaehlerDifferential.D k P.left p) := rfl

/-- The unit-middle value of the coefficient cotangent comparison.

The comparison sends `m ⊗ (1 ⊗ dp)` to `up(m ⊗ dp)`. -/
theorem nativeCoefficientLevelIso_one_D (P : Over B) (m : M) (p : P.left) :
    (nativeCoefficientLevelIso k B M P).hom.hom
      (m ⊗ₜ[B] ((1 : B) ⊗ₜ[P.left] KaehlerDifferential.D k P.left p)) =
        ULift.up (m ⊗ₜ[P.left] KaehlerDifferential.D k P.left p) := by
  let z : M ⊗[P.left] KaehlerDifferential k P.left := m ⊗ₜ[P.left] KaehlerDifferential.D k P.left p
  have h : (1 : B) • m = m := one_smul B m
  have ht : ((1 : B) • m) ⊗ₜ[P.left] KaehlerDifferential.D k P.left p = z :=
    congrArg (fun m' : M => m' ⊗ₜ[P.left] KaehlerDifferential.D k P.left p) h
  exact (nativeCoefficientLevelIso_tmul_D k B M P m 1 p).trans (congrArg ULift.up ht)

/-- The inverse differential-tensor value of the cotangent comparison.

The inverse comparison sends `up(m ⊗ dp)` to `m ⊗ (1 ⊗ dp)`. -/
theorem nativeCoefficientLevelIso_inv_D (P : Over B) (m : M) (p : P.left) :
    (nativeCoefficientLevelIso k B M P).inv.hom
      (ULift.up (m ⊗ₜ[P.left] KaehlerDifferential.D k P.left p)) =
        m ⊗ₜ[B] ((1 : B) ⊗ₜ[P.left] KaehlerDifferential.D k P.left p) := by
  let e := nativeCoefficientLevelIso k B M P
  let x : (nativeGroundCoefficientFunctor k B M).obj P :=
    m ⊗ₜ[B] ((1 : B) ⊗ₜ[P.left] KaehlerDifferential.D k P.left p)
  have h : e.hom.hom x = ULift.up (m ⊗ₜ[P.left] KaehlerDifferential.D k P.left p) :=
    nativeCoefficientLevelIso_one_D k B M P m p
  exact (congrArg e.inv.hom h.symm).trans (ModuleCat.inv_hom_apply e x)

omit [Algebra ℚ k] [Module k M] [SMulCommClass k B M] [IsScalarTower k B M] in
/-- The differential formula for a ground coefficient cotangent map.

For `f : P → Q` over `B`, the map sends `m ⊗ (1 ⊗ dp)` to `m ⊗ (1 ⊗ d(f(p)))`. -/
theorem nativeGroundCoefficientFunctor_map_D {P Q : Over B} (f : P ⟶ Q) (m : M) (p : P.left) :
    ((nativeGroundCoefficientFunctor k B M).map f).hom
      (m ⊗ₜ[B] ((1 : B) ⊗ₜ[P.left] KaehlerDifferential.D k P.left p)) =
        m ⊗ₜ[B] ((1 : B) ⊗ₜ[Q.left] KaehlerDifferential.D k Q.left (f.left.hom p)) := by
  change m ⊗ₜ[B] (CommAlgCat.cotangentMap k B f).hom
      ((1 : B) ⊗ₜ[P.left] KaehlerDifferential.D k P.left p) = _
  exact congrArg (fun x => m ⊗ₜ[B] x) (CommAlgCat.cotangentMap_tensor k B f 1 p)

/-- The proper-quotient augmentation into a coefficient cotangent tensor.

The degree-zero term of the positive-index proper quotient maps to `M ⊗[B] (B ⊗[P] Ω[P/k])` by
its cotangent augmentation and inverse tensor comparison. -/
def nativeScalarAugmentation (P : Over B) :
    (complex k B M P).X 0 ⟶ (nativeGroundCoefficientFunctor k B M).obj P :=
  scalarAugmentation k B M P ≫ (nativeCoefficientLevelIso k B M P).inv

/-- Surjectivity of the coefficient cotangent tensor augmentation.

The proper-quotient augmentation to the coefficient cotangent tensor object is epic, since the
universal-differential augmentation is epic and the tensor comparison is an isomorphism. -/
local instance nativeScalarAugmentation_epi (P : Over B) : Epi (nativeScalarAugmentation k B M P) := by
  unfold nativeScalarAugmentation
  infer_instance

/-- The representative formula for the coefficient cotangent augmentation.

The proper quotient class of the degree-one word `m ⊗ p` maps to `m ⊗ (1 ⊗ dp)`. -/
theorem nativeScalarAugmentation_tprod (P : Over B) (m : M) (a : Fin 1 → P.left) :
    (nativeScalarAugmentation k B M P).hom
      ((rawPositiveRelations k P.left M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
        m ⊗ₜ[B] ((1 : B) ⊗ₜ[P.left] KaehlerDifferential.D k P.left (a 0)) := by
  exact (congrArg (nativeCoefficientLevelIso k B M P).inv.hom
    (properCotangentScalarAugmentation_tprod k P.left M m a)).trans
      (nativeCoefficientLevelIso_inv_D k B M P m (a 0))

/-- The differential formula for the lifted coefficient cotangent target map.

For `f : P → Q` over `B`, the target map sends `up(m ⊗ dp)` to `up(m ⊗ d(f(p)))`. -/
theorem cotangentMap_D {P Q : Over B} (f : P ⟶ Q) (m : M) (p : P.left) :
    (cotangentMap k B M f).hom (ULift.up (m ⊗ₜ[P.left] KaehlerDifferential.D k P.left p)) =
      ULift.up (m ⊗ₜ[Q.left] KaehlerDifferential.D k Q.left (f.left.hom p)) := by
  let z : (complex k B M P).X 0 :=
    (rawPositiveRelations k P.left M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => p))
  have hs := properCotangentScalarAugmentation_tprod k P.left M m (fun _ : Fin 1 => p)
  have ht := properCotangentScalarAugmentation_tprod k Q.left M m (fun _ : Fin 1 => f.left.hom p)
  have hmap : ((map k B M f).f 0).hom z =
      (rawPositiveRelations k Q.left M 1).mkQ
        (m ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => f.left.hom p)) := by
    exact (quotientLinearMap_mkQ k f.left.hom (LinearMap.id : M →ₗ[k] M) 1
      (m ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => p))).trans
        (congrArg (rawPositiveRelations k Q.left M 1).mkQ
          (ModuleCat.Algebra.Hochschild.linearMap_tprod f.left.hom.toNonUnitalAlgHom LinearMap.id 1 m (fun _ => p)))
  have hn := ConcreteCategory.congr_hom (scalarAugmentation_naturality k B M f) z
  exact (congrArg (cotangentMap k B M f).hom hs.symm).trans
    (hn.symm.trans ((congrArg (scalarAugmentation k B M Q).hom hmap).trans ht))

/-- Naturality of the coefficient cotangent tensor comparison.

For an algebra map over `B`, the ground coefficient tensor map followed by the target
comparison equals the source comparison followed by the lifted coefficient cotangent map. -/
@[reassoc]
theorem nativeCoefficientLevelIso_naturality {P Q : Over B} (f : P ⟶ Q) :
    (nativeGroundCoefficientFunctor k B M).map f ≫ (nativeCoefficientLevelIso k B M Q).hom =
      (nativeCoefficientLevelIso k B M P).hom ≫ cotangentMap k B M f := by
  apply (cancel_epi (nativeScalarAugmentation k B M P)).mp
  apply ModuleCat.hom_ext
  let l := ((nativeScalarAugmentation k B M P) ≫
    ((nativeGroundCoefficientFunctor k B M).map f ≫ (nativeCoefficientLevelIso k B M Q).hom)).hom
  let r := ((nativeScalarAugmentation k B M P) ≫
    ((nativeCoefficientLevelIso k B M P).hom ≫ cotangentMap k B M f)).hom
  let π := (rawPositiveRelations k P.left M 1).mkQ
  have h : l.comp π = r.comp π := by
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m a
    have hψ := nativeScalarAugmentation_tprod k B M P m a
    have hN := nativeGroundCoefficientFunctor_map_D k B M f m (a 0)
    have hT := nativeCoefficientLevelIso_tmul_D k B M Q m 1 (f.left.hom (a 0))
    have hS := nativeCoefficientLevelIso_tmul_D k B M P m 1 (a 0)
    have hO := cotangentMap_D k B M f m (a 0)
    change (nativeCoefficientLevelIso k B M Q).hom.hom
        (((nativeGroundCoefficientFunctor k B M).map f).hom
          ((nativeScalarAugmentation k B M P).hom (π (m ⊗ₜ[k] PiTensorProduct.tprod k a)))) =
      (cotangentMap k B M f).hom ((nativeCoefficientLevelIso k B M P).hom.hom
        ((nativeScalarAugmentation k B M P).hom (π (m ⊗ₜ[k] PiTensorProduct.tprod k a))))
    have hT' := hT.trans
      (congrArg (fun z : M => ULift.up (z ⊗ₜ[Q.left] KaehlerDifferential.D k Q.left (f.left.hom (a 0))))
        (one_smul B m))
    have hS' := hS.trans
      (congrArg (fun z : M => ULift.up (z ⊗ₜ[P.left] KaehlerDifferential.D k P.left (a 0)))
        (one_smul B m))
    exact (congrArg (nativeCoefficientLevelIso k B M Q).hom.hom
      ((congrArg ((nativeGroundCoefficientFunctor k B M).map f).hom hψ).trans hN)).trans
        (hT'.trans (hO.symm.trans
          (congrArg (cotangentMap k B M f).hom
            ((congrArg (nativeCoefficientLevelIso k B M P).hom.hom hψ).trans hS')).symm))
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (rawPositiveRelations k P.left M 1).mkQ_surjective z
  exact LinearMap.congr_fun h x

/-- The natural coefficient cotangent target isomorphism.

The degreewise tensor-cancellation comparisons give a natural isomorphism from the ground-
restricted left-coefficient cotangent functor to the lifted cotangent target functor. -/
def nativeCoefficientFunctorIso : nativeGroundCoefficientFunctor k B M ≅ cotangentFunctor k B M :=
  NatIso.ofComponents (nativeCoefficientLevelIso k B M) (nativeCoefficientLevelIso_naturality k B M)

/-- The coefficient cotangent comparison on a simplicial algebra diagram.

For `P_• → B`, the natural coefficient cotangent comparison identifies the degreewise ground
tensor diagram with the lifted simplicial cotangent target diagram. -/
def simplicialNativeCotangentIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    Over.lift P.left P.hom ⋙ nativeGroundCoefficientFunctor k B M ≅ simplicialCotangentDiagram k B M P :=
  Functor.isoWhiskerLeft (Over.lift P.left P.hom) (nativeCoefficientFunctorIso k B M)

/-- The polynomial cotangent simplicial module of the target algebra.

At the identity augmentation of `B`, the polynomial cotangent simplicial functor gives the
simplicial `B`-module used to define `L_{B/k}`. -/
abbrev canonicalNativeCotangentDiagram : SimplicialObject (ModuleCat.{max u v} B) :=
  (CommAlgCat.polynomialCotangentSimplicialFunctor k B).obj (Over.mk (𝟙 B))

/-- The ground coefficient functor on target-algebra modules.

Tensor a `B`-module with `M` on the left over `B`, then restrict scalars along `k → B`, with
the joint ring, algebra, and coefficient carrier universe. -/
abbrev coefficientGroundFunctor : ModuleCat.{max u v} B ⥤ ModuleCat.{max u v w} k :=
  (ModuleCat.tensorBifunctorAt.{max u v, w, max u v} B).obj (ModuleCat.of B M) ⋙
    ModuleCat.restrictScalars (algebraMap k B)

/-- The ground coefficient cotangent chain model.

This is the ground restriction of `M ⊗[B] L_{B/k}`, where `L_{B/k}` is the normalized
polynomial cotangent complex. -/
abbrev canonicalGroundCoefficientComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap k B)).mapHomologicalComplex (.down ℕ)).obj
    ((CommAlgCat.cotangentCoefficientComplexFunctor k B).obj (ModuleCat.of B M))

/-- The additive normalization comparison for coefficient cotangent chains.

The ground coefficient chain model is isomorphic to normalized Moore chains of the coefficient
cotangent diagram on the polynomial resolution of `B`. -/
def canonicalCoefficientNormalizationIso : canonicalGroundCoefficientComplex k B M ≅
    (normalizedMooreComplex (ModuleCat.{max u v w} k)).obj
      (simplicialCotangentDiagram k B M
        ((CommAlgCat.polynomialResolutionOverFunctor.{u, v} k B).obj (Over.mk (𝟙 B)))) :=
  ((CategoryTheory.Functor.mapHomologicalComplexCompIso
    (Iso.refl (coefficientGroundFunctor k B M)) (.down ℕ)).app
      (CommAlgCat.cotangentComplex k B)).symm ≪≫
    ((NormalizedQuotient.mooreCompMapIso (coefficientGroundFunctor k B M)).app (canonicalNativeCotangentDiagram k B)) ≪≫
    (normalizedMooreComplex (ModuleCat.{max u v w} k)).mapIso
      (simplicialNativeCotangentIso k B M
        ((CommAlgCat.polynomialResolutionOverFunctor.{u, v} k B).obj (Over.mk (𝟙 B))))

/-- The normalized-to-alternating homotopy comparison for coefficient cotangents.

The coefficient normalization isomorphism followed by the Dold–Kan comparison gives a homotopy
equivalence from the ground coefficient cotangent complex to the alternating-face cotangent
complex. -/
def canonicalCoefficientAlternatingHomotopyEquiv :
    HomotopyEquiv (canonicalGroundCoefficientComplex k B M)
      ((alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj
        (simplicialCotangentDiagram k B M
          ((CommAlgCat.polynomialResolutionOverFunctor.{u, v} k B).obj (Over.mk (𝟙 B))))) :=
  (HomotopyEquiv.ofIso (canonicalCoefficientNormalizationIso k B M)).trans
    (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (Y := simplicialCotangentDiagram k B M
        ((CommAlgCat.polynomialResolutionOverFunctor.{u, v} k B).obj (Over.mk (𝟙 B)))))

/-- The forward map of the coefficient cotangent homotopy comparison.

The forward chain map is the coefficient normalization isomorphism followed by the inclusion
of normalized Moore chains into the alternating-face complex. -/
theorem canonicalCoefficientAlternatingHomotopyEquiv_hom :
    (canonicalCoefficientAlternatingHomotopyEquiv k B M).hom =
      (canonicalCoefficientNormalizationIso k B M).hom ≫
        inclusionOfMooreComplexMap
          (simplicialCotangentDiagram k B M
            ((CommAlgCat.polynomialResolutionOverFunctor.{u, v} k B).obj (Over.mk (𝟙 B)))) := rfl

/-- The homology comparison for normalized and alternating coefficient cotangents.

The coefficient cotangent homotopy equivalence induces an isomorphism on homology in every
nonnegative degree. -/
def canonicalCoefficientAlternatingHomologyIso (n : ℕ) :
    (canonicalGroundCoefficientComplex k B M).homology n ≅
      ((alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj
        (simplicialCotangentDiagram k B M
          ((CommAlgCat.polynomialResolutionOverFunctor.{u, v} k B).obj (Over.mk (𝟙 B))))).homology n :=
  _root_.isoOfQuasiIsoAt (canonicalCoefficientAlternatingHomotopyEquiv k B M).hom n

/-- The ground-scalar André–Quillen coefficient homology comparison.

Homology of the ground-restricted complex `M ⊗[B] L_{B/k}` is isomorphic to restriction of the
André–Quillen homology `D_n(B/k;M)` along `k → B`. -/
def canonicalGroundAndreQuillenHomologyIso (n : ℕ) :
    (canonicalGroundCoefficientComplex k B M).homology n ≅
      (ModuleCat.restrictScalars (algebraMap k B)).obj
        (CommAlgCat.andreQuillenHomology k B (ModuleCat.of B M) n) :=
  (((CommAlgCat.cotangentCoefficientComplexFunctor k B).obj (ModuleCat.of B M)).sc n).mapHomologyIso
    (ModuleCat.restrictScalars (algebraMap k B))

end ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.AugmentedAlgebra
