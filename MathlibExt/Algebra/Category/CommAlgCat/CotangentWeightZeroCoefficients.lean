/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentWeightZero
public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Whiskering

/-!
# Weight-zero cotangent coefficients and their homology

Let `k : Type u` be a commutative ring, `A : CommAlgCat.{max u v} k`, and `M : ModuleCat.{t}
A`. At an algebra `P→A`, the coefficient module `M ⊗_A (A ⊗_P P)` is canonically equivalent to
`M`. As an object in the joint carrier category it is identified with `ULift.{max u v} M`, and
`m ⊗ (a ⊗ p)` maps to the lift of `(P.hom(p)·a)·m`.

For any simplicial algebra augmented to constant `A`, these regular-module unitors commute
with all simplicial operators, augmented-algebra maps, and coefficient maps. The tensor family
is naturally the constant lifted coefficient. Moore normalization identifies its degree-zero
homology with that coefficient and gives zero homology in positive degrees.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial TensorProduct ChangeOfRings

universe u v t

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. The functor
`cotangentWeightZeroCoefficientLift k A : ModuleCat.{t} A → ModuleCat.{max u v t} A` sends `M`
to `ULift.{max u v} M`, with the transported `A`-action, and sends a coefficient map to its
lifted linear map. -/
abbrev cotangentWeightZeroCoefficientLift :
    ModuleCat.{t} A ⥤ ModuleCat.{max u v t} A :=
  ModuleCat.uliftFunctor.{max u v, t} A

/-- Let `k : Type u` be a commutative ring, `A : CommAlgCat.{max u v} k`, and `M : ModuleCat.{t}
A`. The isomorphism `M ⊗_A A ≅ ULift.{max u v} M` in the joint carrier category is the regular
tensor unitor followed by the coefficient lift. It sends `m ⊗ a` to `ULift.up (a • m)`. -/
def cotangentWeightZeroCoefficientRegularIso (M : ModuleCat.{t} A) :
    ((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).obj
        (ModuleCat.of A A) ≅
      (cotangentWeightZeroCoefficientLift.{u, v, t} k A).obj M :=
  ((TensorProduct.rid A M).trans (ULift.moduleEquiv (R := A) (M := M)).symm).toModuleIso

/-- Let `k : Type u` be a commutative ring, `A : CommAlgCat.{max u v} k`, `P∈Over A`, and `M :
ModuleCat.{t} A`. The isomorphism `M ⊗_A (A ⊗_{P.left} P.left) ≅ ULift.{max u v} M` is the
weight-zero regular unitor followed by the coefficient universe lift. It is
`cotangentWeightZeroCoefficientLevelIso k A P M`. -/
def cotangentWeightZeroCoefficientLevelIso (P : Over A) (M : ModuleCat.{t} A) :
    ((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).obj
        (cotangentWeightZeroLevel k A P) ≅
      (cotangentWeightZeroCoefficientLift.{u, v, t} k A).obj M :=
  ((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapIso
      (cotangentWeightZeroLevelIso k A P) ≪≫
    cotangentWeightZeroCoefficientRegularIso.{u, v, t} k A M

@[simp]
theorem cotangentWeightZeroCoefficientLevelIso_tmul
    (P : Over A) (M : ModuleCat.{t} A) (m : M) (x : cotangentWeightZeroLevel k A P) :
    (cotangentWeightZeroCoefficientLevelIso.{u, v, t} k A P M).hom.hom (m ⊗ₜ[A] x) =
      ULift.up ((cotangentWeightZeroLevelIso k A P).hom.hom x • m) := rfl

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `P∈Over A`, and `M` an `A`-module. For
`m∈M`, `a∈A`, and `p∈P.left`, the level isomorphism sends `m ⊗_A (a ⊗_{P.left} p)` to
`ULift.up ((P.hom(p) * a) • m)`. The source action of `P.left` on `A` is induced by its
augmentation. -/
@[simp]
theorem cotangentWeightZeroCoefficientLevelIso_tmul_tmul
    (P : Over A) (M : ModuleCat.{t} A) (m : M) (a : A) (p : P.left) :
    (cotangentWeightZeroCoefficientLevelIso.{u, v, t} k A P M).hom.hom
      (m ⊗ₜ[A] (a ⊗ₜ[P.left,P.hom.hom.toRingHom] p)) =
        ULift.up ((P.hom.hom p * a) • m) := by
  let x : cotangentWeightZeroLevel k A P := a ⊗ₜ[P.left,P.hom.hom.toRingHom] p
  have h := cotangentWeightZeroCoefficientLevelIso_tmul.{u, v, t} k A P M m x
  have hx := cotangentWeightZeroLevelIso_tmul.{u, v} k A P a p
  exact h.trans (congrArg (fun a : A => ULift.up (a • m)) hx)

/-- For a commutative ring `k`, a `k`-algebra `A`, `P∈Over A`, and any coefficient module `M :
ModuleCat.{t} A`, there is an `A`-linear equivalence `M ⊗_A cotangentWeightZeroLevel k A P
≃ₗ[A] M`. It is the level isomorphism followed by `ULift.moduleEquiv`, removing the
categorical universe lift. -/
def cotangentWeightZeroCoefficientLevelLinearEquiv (P : Over A) (M : ModuleCat.{t} A) :
    (M ⊗[A] cotangentWeightZeroLevel k A P) ≃ₗ[A] M :=
  (cotangentWeightZeroCoefficientLevelIso.{u, v, t} k A P M).toLinearEquiv.trans ULift.moduleEquiv

@[simp]
theorem cotangentWeightZeroCoefficientLevelLinearEquiv_tmul_tmul
    (P : Over A) (M : ModuleCat.{t} A) (m : M) (a : A) (p : P.left) :
    cotangentWeightZeroCoefficientLevelLinearEquiv k A P M
      (m ⊗ₜ[A] (a ⊗ₜ[P.left,P.hom.hom.toRingHom] p)) = (P.hom.hom p * a) • m := by
  change ((cotangentWeightZeroCoefficientLevelIso.{u, v, t} k A P M).hom.hom
    (m ⊗ₜ[A] (a ⊗ₜ[P.left,P.hom.hom.toRingHom] p))).down = _
  rw [cotangentWeightZeroCoefficientLevelIso_tmul_tmul]

/-- Let `k` be a commutative ring, `A` a `k`-algebra, and `f : P → Q` in `Over A`. The
regular-module comparisons satisfy `cotangentWeightZeroTransport k A f ≫
(cotangentWeightZeroLevelIso k A Q).hom = (cotangentWeightZeroLevelIso k A P).hom`. The map on
tensors is `a⊗p ↦ a⊗f.left(p)`, and augmentation compatibility makes its value in `A`
unchanged. -/
@[reassoc]
theorem cotangentWeightZeroTransport_comp_levelIso {P Q : Over A} (f : P ⟶ Q) :
    cotangentWeightZeroTransport k A f ≫ (cotangentWeightZeroLevelIso k A Q).hom =
      (cotangentWeightZeroLevelIso k A P).hom := by
  unfold cotangentWeightZeroTransport
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. The bifunctor takes
`M : ModuleCat.{t} A` and a simplicial algebra `P` augmented to constant `A` to the simplicial
`A`-module with degree `i` equal to `M ⊗_A (A ⊗_{P_i} P_i)`. Coefficient maps act in the first
factor, and simplicial operators and augmented-algebra maps act by weight-zero transport in
the second. -/
def cotangentWeightZeroTensorFamily :
    ModuleCat.{t} A ⥤
      Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A) ⥤
        SimplicialObject (ModuleCat.{max u v t} A) :=
  ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A ⋙
    SimplicialObject.whiskering (ModuleCat.{max u v} A) (ModuleCat.{max u v t} A) ⋙
      (Functor.whiskeringLeft
        (Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
        (SimplicialObject (ModuleCat.{max u v} A))
        (SimplicialObject (ModuleCat.{max u v t} A))).obj
          (cotangentWeightZeroResolutionFunctor k A)

/-- For a commutative ring `k`, a `k`-algebra `A`, and coefficient modules `M : ModuleCat.{t} A`,
the bifunctor `cotangentWeightZeroConstantCoefficientFamily k A` sends every augmented
simplicial algebra over constant `A` to the constant simplicial module on `ULift.{max u v} M`.
Coefficient maps act by their lifted maps. -/
def cotangentWeightZeroConstantCoefficientFamily :
    ModuleCat.{t} A ⥤
      Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A) ⥤
        SimplicialObject (ModuleCat.{max u v t} A) :=
  cotangentWeightZeroCoefficientLift.{u, v, t} k A ⋙
    SimplicialObject.const (ModuleCat.{max u v t} A) ⋙
      Functor.const (Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `P` any simplicial algebra augmented to
constant `A`, and `M : ModuleCat.{t} A`. The simplicial tensor family `M ⊗_A (A ⊗_{P_i} P_i)`
is isomorphic to the constant simplicial module on `ULift.{max u v} M`. Its components are the
level regular-module unitors, and they commute with every simplicial operator. -/
def cotangentWeightZeroTensorSimplicialIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (M : ModuleCat.{t} A) :
    ((cotangentWeightZeroTensorFamily.{u, v, t} k A).obj M).obj P ≅
      (SimplicialObject.const (ModuleCat.{max u v t} A)).obj
        ((cotangentWeightZeroCoefficientLift.{u, v, t} k A).obj M) :=
  let F := (ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M
  Functor.isoWhiskerRight (cotangentWeightZeroOnResolutionIso.{u, v} k A P) F ≪≫
    Functor.constComp SimplexCategoryᵒᵖ (ModuleCat.of A A) F ≪≫
      (SimplicialObject.const (ModuleCat.{max u v t} A)).mapIso
        (cotangentWeightZeroCoefficientRegularIso.{u, v, t} k A M)

/-- Let `P` be a simplicial `k`-algebra augmented to constant `A` by maps `ε_i:P_i→A`, and let `M`
be any `A`-module. For `i : SimplexCategoryᵒᵖ`, `m∈M`, `a∈A`, and `p∈P_i`, the component of
the weight-zero simplicial isomorphism sends `m ⊗_A (a ⊗_{P_i} p)` to `ULift.up ((ε_i(p) * a)
• m)`. -/
@[simp]
theorem cotangentWeightZeroTensorSimplicialIso_tmul_tmul
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (M : ModuleCat.{t} A) (i : SimplexCategoryᵒᵖ) (m : M) (a : A)
    (p : (Over.mk (P.hom.app i) : Over A).left) :
    ((cotangentWeightZeroTensorSimplicialIso.{u, v, t} k A P M).hom.app i).hom
      (m ⊗ₜ[A] (a ⊗ₜ[(Over.mk (P.hom.app i) : Over A).left,
        (P.hom.app i).hom.toRingHom] p)) =
        ULift.up (((show A from (P.hom.app i).hom p) * a) • m) :=
  cotangentWeightZeroCoefficientLevelIso_tmul_tmul k A (Over.mk (P.hom.app i)) M m a p

/-- Let `P,Q` be simplicial `k`-algebras augmented to constant `A`, `f : P → Q` an
augmentation-preserving simplicial map, and `M` any `A`-module. For the coefficient tensor
family `F_M` and its constant-coefficient isomorphisms `η_P,η_Q`, `F_M(f) ≫ η_Q.hom =
η_P.hom`. The constant target coefficient is independent of the augmented algebra. -/
@[reassoc]
theorem cotangentWeightZeroTensorSimplicialIso_resolution_naturality
    {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
    (f : P ⟶ Q) (M : ModuleCat.{t} A) :
    ((cotangentWeightZeroTensorFamily.{u, v, t} k A).obj M).map f ≫
      (cotangentWeightZeroTensorSimplicialIso.{u, v, t} k A Q M).hom =
        (cotangentWeightZeroTensorSimplicialIso.{u, v, t} k A P M).hom := by
  apply NatTrans.ext
  funext i
  let F := (ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M
  change F.map ((cotangentWeightZeroOnResolutionMap k A f).app i) ≫
      (F.map (cotangentWeightZeroLevelIso k A (Over.mk (Q.hom.app i))).hom ≫
        (cotangentWeightZeroCoefficientRegularIso.{u, v, t} k A M).hom) =
    F.map (cotangentWeightZeroLevelIso k A (Over.mk (P.hom.app i))).hom ≫
      (cotangentWeightZeroCoefficientRegularIso.{u, v, t} k A M).hom
  have h := NatTrans.congr_app
    ((cotangentWeightZeroResolutionFunctorIso.{u, v} k A).hom.naturality f) i
  change (cotangentWeightZeroOnResolutionMap k A f).app i ≫
      (cotangentWeightZeroLevelIso k A (Over.mk (Q.hom.app i))).hom =
    (cotangentWeightZeroLevelIso k A (Over.mk (P.hom.app i))).hom at h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (cotangentWeightZeroCoefficientRegularIso.{u, v, t} k A M).hom)
      ((F.map_comp _ _).symm.trans (congrArg F.map h))))

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `P∈Over A`, and `f : M → N` a map of
`A`-modules of carrier universe `t`. For the weight-zero regular level `Z_P=A ⊗_{P.left}
P.left` and comparison `η_M : M ⊗_A Z_P ≅ Lift M`, `(f ⊗ 𝟙 Z_P) ≫ η_N.hom = η_M.hom ≫
Lift(f)`. -/
@[reassoc]
theorem cotangentWeightZeroCoefficientLevelIso_naturality
    (P : Over A) {M N : ModuleCat.{t} A} (f : M ⟶ N) :
    ((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).map f).app
        (cotangentWeightZeroLevel k A P) ≫
      (cotangentWeightZeroCoefficientLevelIso.{u, v, t} k A P N).hom =
        (cotangentWeightZeroCoefficientLevelIso.{u, v, t} k A P M).hom ≫
          (cotangentWeightZeroCoefficientLift.{u, v, t} k A).map f := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m x
  change ULift.up ((cotangentWeightZeroLevelIso k A P).hom.hom x • f.hom m) =
    ULift.up (f.hom ((cotangentWeightZeroLevelIso k A P).hom.hom x • m))
  exact congrArg ULift.up (f.hom.map_smul _ _).symm

/-- Let `k` be a commutative ring and `A` a `k`-algebra. The bifunctor taking a coefficient `M`
and a simplicial algebra augmented to `A` to the simplicial module `M ⊗_A (A ⊗_{P_i} P_i)` is
naturally isomorphic to the constant simplicial lifted-coefficient bifunctor. Its components
are the weight-zero simplicial unitors, natural in coefficient maps and augmented-algebra maps
together. -/
def cotangentWeightZeroTensorFamilyIso :
    cotangentWeightZeroTensorFamily.{u, v, t} k A ≅
      cotangentWeightZeroConstantCoefficientFamily k A :=
  NatIso.ofComponents
    (fun M => NatIso.ofComponents (fun P => cotangentWeightZeroTensorSimplicialIso.{u, v, t} k A P M)
      (by
        intro P Q f
        have h := cotangentWeightZeroTensorSimplicialIso_resolution_naturality k A f M
        exact h.trans (Category.comp_id _).symm))
    (by
      intro M N f
      apply NatTrans.ext
      funext P
      apply NatTrans.ext
      funext i
      exact cotangentWeightZeroCoefficientLevelIso_naturality k A (Over.mk (P.hom.app i)) f)

/-- For a commutative ring `k : Type u`, `A : CommAlgCat.{max u v} k`, and a simplicial algebra
`P` augmented to constant `A`, `cotangentWeightZeroTensorComplexFunctor k A P` sends `M :
ModuleCat.{t} A` to the normalized Moore complex of the degreewise tensors `M ⊗_A (A ⊗_{P_i}
P_i)`. Its target is `ChainComplex (ModuleCat.{max u v t} A) ℕ`. -/
def cotangentWeightZeroTensorComplexFunctor
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    ModuleCat.{t} A ⥤ ChainComplex (ModuleCat.{max u v t} A) ℕ :=
  cotangentWeightZeroTensorFamily.{u, v, t} k A ⋙
    (evaluation
      (Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
      (SimplicialObject (ModuleCat.{max u v t} A))).obj P ⋙
        normalizedMooreComplex (ModuleCat.{max u v t} A)

/-- Let `P` be any simplicial `k`-algebra augmented to `A`, and `M` any `A`-module. Moore
normalization of the weight-zero simplicial tensor isomorphism gives an isomorphism from
`cotangentWeightZeroTensorComplexFunctor k A P M` to the normalized constant complex on `Lift
M`, namely `cotangentWeightZeroCoefficientComplexFunctor k A (Lift M)`. -/
def cotangentWeightZeroTensorComplexIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (M : ModuleCat.{t} A) :
    (cotangentWeightZeroTensorComplexFunctor k A P).obj M ≅
      (cotangentWeightZeroCoefficientComplexFunctor k A).obj
        ((cotangentWeightZeroCoefficientLift.{u, v, t} k A).obj M) :=
  (normalizedMooreComplex (ModuleCat.{max u v t} A)).mapIso
    (cotangentWeightZeroTensorSimplicialIso.{u, v, t} k A P M)

/-- For a commutative ring `k`, a `k`-algebra `A`, and a fixed simplicial algebra `P` augmented to
`A`, there is a natural isomorphism of coefficient functors
`cotangentWeightZeroTensorComplexFunctor k A P ≅ cotangentWeightZeroCoefficientLift k A ⋙
cotangentWeightZeroCoefficientComplexFunctor k A`. Its component is the normalization of the
simplicial regular-module unitor. -/
def cotangentWeightZeroTensorComplexNatIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    cotangentWeightZeroTensorComplexFunctor.{u, v, t} k A P ≅
      cotangentWeightZeroCoefficientLift.{u, v, t} k A ⋙
        cotangentWeightZeroCoefficientComplexFunctor k A :=
  NatIso.ofComponents (cotangentWeightZeroTensorComplexIso k A P) (by
    intro M N f
    let E := (cotangentWeightZeroTensorFamilyIso k A).hom.naturality f
    have h := NatTrans.congr_app E P
    change (normalizedMooreComplex (ModuleCat.{max u v t} A)).map _ ≫
        (normalizedMooreComplex (ModuleCat.{max u v t} A)).map _ =
      (normalizedMooreComplex (ModuleCat.{max u v t} A)).map _ ≫
        (normalizedMooreComplex (ModuleCat.{max u v t} A)).map _
    let F := normalizedMooreComplex (ModuleCat.{max u v t} A)
    exact (F.map_comp _ _).symm.trans
      ((congrArg F.map h).trans (F.map_comp _ _)))

/-- Let `f : P → Q` be a morphism of simplicial `k`-algebras augmented to constant `A`, and `M`
any `A`-module. The normalized map of the weight-zero tensor family, followed by the
comparison for `Q`, equals the comparison for `P`: `N(F_M(f)) ≫ η_Q.hom = η_P.hom`. Here both
targets are the normalized constant complex on `Lift M`. -/
@[reassoc]
theorem cotangentWeightZeroTensorComplexIso_resolution_naturality
    {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
    (f : P ⟶ Q) (M : ModuleCat.{t} A) :
    (normalizedMooreComplex (ModuleCat.{max u v t} A)).map
        (((cotangentWeightZeroTensorFamily.{u, v, t} k A).obj M).map f) ≫
      (cotangentWeightZeroTensorComplexIso k A Q M).hom =
        (cotangentWeightZeroTensorComplexIso k A P M).hom := by
  let F := normalizedMooreComplex (ModuleCat.{max u v t} A)
  have h := cotangentWeightZeroTensorSimplicialIso_resolution_naturality.{u, v, t} k A f M
  exact (F.map_comp _ _).symm.trans (congrArg F.map h)

/-- For a commutative ring `k : Type u`, `A : CommAlgCat.{max u v} k`, a simplicial algebra `P`
augmented to `A`, and `n : ℕ`, the functor `cotangentWeightZeroTensorHomologyFunctor k A P n :
ModuleCat.{t} A → ModuleCat.{max u v t} A` takes degree-`n` homology of the normalized tensor
complex `M ⊗_A (A ⊗_{P_i} P_i)`. -/
def cotangentWeightZeroTensorHomologyFunctor
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) (n : ℕ) :
    ModuleCat.{t} A ⥤ ModuleCat.{max u v t} A :=
  cotangentWeightZeroTensorComplexFunctor k A P ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{max u v t} A) (ComplexShape.down ℕ) n

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `P` any simplicial algebra augmented to `A`,
and `n : ℕ`. The coefficient functor taking `H_n` of the normalized weight-zero tensor family
is naturally isomorphic to the coefficient lift followed by
`andreQuillenWeightZeroHomologyFunctor k A n`. This is the homology image of the normalized
constant-coefficient comparison. -/
def cotangentWeightZeroTensorHomologyNatIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) (n : ℕ) :
    cotangentWeightZeroTensorHomologyFunctor.{u, v, t} k A P n ≅
      cotangentWeightZeroCoefficientLift.{u, v, t} k A ⋙ andreQuillenWeightZeroHomologyFunctor k A n :=
  Functor.isoWhiskerRight (cotangentWeightZeroTensorComplexNatIso k A P)
    (HomologicalComplex.homologyFunctor (ModuleCat.{max u v t} A) (ComplexShape.down ℕ) n)

/-- Let `k : Type u` be a commutative ring, `A : CommAlgCat.{max u v} k`, and `P` any simplicial
algebra augmented to `A`. As coefficient functors, `cotangentWeightZeroTensorHomologyFunctor k
A P 0 ≅ cotangentWeightZeroCoefficientLift k A`. Thus degree-zero homology of the normalized
tensor family is naturally `ULift.{max u v} M` at coefficient `M`. -/
def cotangentWeightZeroTensorHomologyZeroNatIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    cotangentWeightZeroTensorHomologyFunctor.{u, v, t} k A P 0 ≅
      cotangentWeightZeroCoefficientLift.{u, v, t} k A :=
  cotangentWeightZeroTensorHomologyNatIso k A P 0 ≪≫
    Functor.isoWhiskerLeft (cotangentWeightZeroCoefficientLift.{u, v, t} k A)
      (andreQuillenWeightZeroHomologyZeroIso.{u, v, max u v t} k A) ≪≫
    NatIso.ofComponents (fun M => Iso.refl _) (by
      intro M N f
      change (𝟭 (ModuleCat.{max u v t} A)).map
        ((cotangentWeightZeroCoefficientLift.{u, v, t} k A).map f) =
        𝟙 _ ≫ (cotangentWeightZeroCoefficientLift.{u, v, t} k A).map f
      exact (Functor.id_map _).trans (Category.id_comp _).symm)

/-- For a commutative ring `k`, a `k`-algebra `A`, any simplicial algebra `P` augmented to `A`,
and `M : ModuleCat.{t} A`, degree-zero homology of the normalized weight-zero tensor complex
is `A`-linearly equivalent to `M`. The equivalence is the lifted-coefficient homology
isomorphism followed by `ULift.moduleEquiv`. -/
def cotangentWeightZeroTensorHomologyZeroLinearEquiv
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (M : ModuleCat.{t} A) :
    (cotangentWeightZeroTensorHomologyFunctor k A P 0).obj M ≃ₗ[A] M :=
  ((cotangentWeightZeroTensorHomologyZeroNatIso k A P).app M).toLinearEquiv.trans
    ULift.moduleEquiv

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `P` any simplicial algebra augmented to `A`,
and `M : ModuleCat.{t} A` any coefficient module. For every `n : ℕ`, `IsZero
(cotangentWeightZeroTensorHomologyFunctor k A P (n+1) M)`. The normalized tensor family is
isomorphic to the constant coefficient complex. -/
theorem cotangentWeightZeroTensorHomology_isZero_succ
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    (M : ModuleCat.{t} A) (n : ℕ) :
    IsZero ((cotangentWeightZeroTensorHomologyFunctor k A P (n + 1)).obj M) :=
  (andreQuillenWeightZeroHomology_isZero_succ k A
    ((cotangentWeightZeroCoefficientLift.{u, v, t} k A).obj M) n).of_iso
      ((cotangentWeightZeroTensorHomologyNatIso k A P (n + 1)).app M)

end CommAlgCat

end
