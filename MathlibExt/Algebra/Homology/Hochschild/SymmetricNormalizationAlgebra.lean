/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricScalarSimplicial
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricAlgebraComplex
public import MathlibExt.Algebra.Homology.Hochschild.PositiveAlgebraCochainKernel
public import MathlibExt.Algebra.Homology.SplitHomotopyKernel
public import MathlibExt.Algebra.Homology.LinearHomCochainHomotopyEquiv

/-!
# Algebra-linear Hochschild normalization

The coefficient-head A-action makes the full raw and normalized
Hochschild complexes A-linear. The normalization projection,
Dold–Kan projector, section and homotopy are A-linear. The tensor
tails A/(k·1) remain ground modules throughout.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- Original factorwise normalization, now as an coefficient-head A-linear map. -/
def algebraNormalizationLevelMap (n : ℕ) :
    M ⊗[k] TensorPower k n A →ₗ[A]
      M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) :=
  TensorProduct.AlgebraTensorModule.lTensor A M
    (PiTensorProduct.map (fun _ : Fin n => (ModuleCat.Algebra.Hochschild.unitSubmodule k A).mkQ))

/-- The A-linear map retains the original exact k-linear normalization. -/
theorem algebraNormalizationLevelMap_restrictScalars (n : ℕ) :
    (algebraNormalizationLevelMap k A M n).restrictScalars k =
      (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A M n).hom := rfl

/-- The native normalization projection is exactly the original A-linear level map restricted to k. -/
theorem nativeNormalizationProjection_f (n : ℕ) :
    (normalizationProjection k A M).f n =
      ModuleCat.ofHom ((algebraNormalizationLevelMap k A M n).restrictScalars k) := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  exact ModuleCat.Algebra.Hochschild.normalizationProjection_f k A M n

/-- Native normalization is actually surjective in its original A-module carrier. -/
theorem algebraNormalizationLevelMap_surjective (n : ℕ) :
    Function.Surjective (algebraNormalizationLevelMap k A M n) :=
  TensorPower.coefficientQuotientMap_surjective (ModuleCat.Algebra.Hochschild.unitSubmodule k A) M n

/-- The native normalized boundary retains the original normalization square on every raw tensor. -/
theorem nativeNormalizationBoundary_apply (n : ℕ)
    (x : M ⊗[k] TensorPower k (n + 1) A) :
    ((normalizedChainComplex k A M).d (n + 1) n).hom
      (algebraNormalizationLevelMap k A M (n + 1) x) =
    algebraNormalizationLevelMap k A M n (algebraBoundary k A M n x) := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  let d : (M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) →ₗ[k]
      M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) :=
    ((normalizedChainComplex k A M).d (n + 1) n).hom
  let p := (algebraNormalizationLevelMap k A M (n + 1)).restrictScalars k
  let q := (algebraNormalizationLevelMap k A M n).restrictScalars k
  let b := (algebraBoundary k A M n).restrictScalars k
  have hb : b = (ModuleCat.Algebra.Hochschild.boundary k A M n).hom := by
    change ((ModuleCat.Algebra.Hochschild.chainComplex k A M).d (n + 1) n).hom = _
    exact congrArg ModuleCat.Hom.hom (ModuleCat.Algebra.Hochschild.chainComplex_d k A M n)
  have h : d.comp p = q.comp (ModuleCat.Algebra.Hochschild.boundary k A M n).hom := by
    exact congrArg ModuleCat.Hom.hom (ModuleCat.Algebra.Hochschild.normalizationLevelMap_d k A M n)
  exact congrArg (fun f : (M ⊗[k] TensorPower k (n + 1) A) →ₗ[k]
    M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) => f x)
      (h.trans (congrArg (fun f => q.comp f) hb.symm))

/-- The original normalized boundary is A-linear by its surjective normalization square. -/
def algebraNormalizedBoundary (n : ℕ) :
    M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) →ₗ[A]
      M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) := by
  let d : (M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) →ₗ[k]
      M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) :=
    ((normalizedChainComplex k A M).d (n + 1) n).hom
  refine { toFun := d, map_add' := d.map_add, map_smul' := ?_ }
  intro a y
  change d (a • y) = a • d y
  obtain ⟨x, rfl⟩ := algebraNormalizationLevelMap_surjective k A M (n + 1) y
  calc
    d (a • algebraNormalizationLevelMap k A M (n + 1) x) =
        d (algebraNormalizationLevelMap k A M (n + 1) (a • x)) :=
      congrArg d ((algebraNormalizationLevelMap k A M (n + 1)).map_smul a x).symm
    _ = algebraNormalizationLevelMap k A M n (algebraBoundary k A M n (a • x)) :=
      nativeNormalizationBoundary_apply k A M n (a • x)
    _ = a • algebraNormalizationLevelMap k A M n (algebraBoundary k A M n x) :=
      (congrArg (algebraNormalizationLevelMap k A M n) ((algebraBoundary k A M n).map_smul a x)).trans
        ((algebraNormalizationLevelMap k A M n).map_smul a (algebraBoundary k A M n x))
    _ = a • d (algebraNormalizationLevelMap k A M (n + 1) x) :=
      congrArg (fun z => a • z) (nativeNormalizationBoundary_apply k A M n x).symm

/-- The original normalized boundary still squares to zero in its A-module structure. -/
theorem algebraNormalizedBoundary_comp (n : ℕ) :
    (algebraNormalizedBoundary k A M n).comp (algebraNormalizedBoundary k A M (n + 1)) = 0 := by
  let d₀ : (M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) →ₗ[k]
      M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) :=
    ((normalizedChainComplex k A M).d (n + 1) n).hom
  let d₁ : (M ⊗[k] TensorPower k (n + 2) (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) →ₗ[k]
      M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) :=
    ((normalizedChainComplex k A M).d (n + 2) (n + 1)).hom
  have h : d₀.comp d₁ = 0 :=
    congrArg ModuleCat.Hom.hom ((normalizedChainComplex k A M).d_comp_d (n + 2) (n + 1) n)
  apply LinearMap.ext
  intro x
  change d₀ (d₁ x) = 0
  exact congrArg (fun f : (M ⊗[k] TensorPower k (n + 2) (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) →ₗ[k]
    M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) => f x) h

/-- The full normalized Hochschild complex over A, with only original ground quotient tails. -/
def algebraNormalizedChainComplex : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  ChainComplex.of
    (fun n => ModuleCat.of A (M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)))
    (fun n => ModuleCat.ofHom (algebraNormalizedBoundary k A M n))
    (fun n => by
      apply ModuleCat.hom_ext
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero] using
        algebraNormalizedBoundary_comp k A M n)

/-- The original normalization projection is an A-linear chain map. -/
def algebraNormalizationProjection : algebraRawComplex k A M ⟶ algebraNormalizedChainComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (algebraNormalizationLevelMap k A M n)) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    dsimp only [algebraNormalizedChainComplex, algebraRawComplex]
    rw [ChainComplex.of_d, ChainComplex.of_d]
    change algebraNormalizedBoundary k A M n (algebraNormalizationLevelMap k A M (n + 1) x) =
      algebraNormalizationLevelMap k A M n (algebraBoundary k A M n x)
    exact nativeNormalizationBoundary_apply k A M n x)

/-- The raw native normalization projector as an A-linear chain map. -/
def algebraRawNativeNormalizationProjector : algebraRawComplex k A M ⟶ algebraRawComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    { toFun := rawNativeNormalizationProjector k A M n
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => rawNativeNormalizationProjector_smul k A M n a x }) (by
        intro n
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        have h := ConcreteCategory.congr_hom
          ((rawNativeNormalizationProjectorComplex k A M).comm (n + 1) n) x
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
          rawNativeNormalizationProjectorComplex_f] at h
        dsimp only [algebraRawComplex]
        rw [ChainComplex.of_d]
        change algebraBoundary k A M n (rawNativeNormalizationProjector k A M (n + 1) x) =
          rawNativeNormalizationProjector k A M n (algebraBoundary k A M n x)
        exact h)

/-- The native normalization projection followed by its inverse is the original raw native projector. -/
theorem normalizationProjection_inverse_eq_rawNativeProjector :
    normalizationProjection k A M ≫ (normalizationHomotopyEquiv k A M).inv =
      rawNativeNormalizationProjectorComplex k A M := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  let X := coefficientBar k A M
  let c : chainComplex k A M ≅
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj X :=
    chainComplexIso k A M
  let e : AlgebraicTopology.NormalizedQuotient.obj X ≅ normalizedChainComplex k A M :=
    ModuleCat.Algebra.Hochschild.normalizationIso k A M
  let r := (AlgebraicTopology.NormalizedQuotient.mooreIso X).hom ≫
    AlgebraicTopology.inclusionOfMooreComplexMap X
  have hpr : AlgebraicTopology.NormalizedQuotient.projection X ≫ r =
      AlgebraicTopology.DoldKan.PInfty (X := X) := by
    change AlgebraicTopology.NormalizedQuotient.projection X ≫
      ((AlgebraicTopology.NormalizedQuotient.mooreIso X).hom ≫
        AlgebraicTopology.inclusionOfMooreComplexMap X) = _
    rw [← Category.assoc, AlgebraicTopology.NormalizedQuotient.projection_mooreIso_hom]
    exact AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap X
  rw [normalizationHomotopyEquiv_inv]
  change ((c.hom ≫ AlgebraicTopology.NormalizedQuotient.projection X) ≫ e.hom) ≫
    ((e.inv ≫ r) ≫ c.inv) = c.hom ≫ AlgebraicTopology.DoldKan.PInfty ≫ c.inv
  calc
    _ = c.hom ≫ (AlgebraicTopology.NormalizedQuotient.projection X ≫ r) ≫ c.inv := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = c.hom ≫ AlgebraicTopology.DoldKan.PInfty ≫ c.inv :=
      congrArg (fun f => c.hom ≫ f ≫ c.inv) hpr

/-- The original normalized inverse is A-linear because it factors the A-linear native projector. -/
def algebraNormalizationInverseLevel (n : ℕ) :
    M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) →ₗ[A]
      M ⊗[k] TensorPower k n A := by
  let i : (M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) →ₗ[k]
      M ⊗[k] TensorPower k n A := ((normalizationHomotopyEquiv k A M).inv.f n).hom
  refine { toFun := i, map_add' := i.map_add, map_smul' := ?_ }
  intro a y
  change i (a • y) = a • i y
  obtain ⟨x, rfl⟩ := algebraNormalizationLevelMap_surjective k A M n y
  let p := (algebraNormalizationLevelMap k A M n).restrictScalars k
  let r := rawNativeNormalizationProjector k A M n
  have hp : ((normalizationProjection k A M).f n).hom = p :=
    congrArg ModuleCat.Hom.hom (nativeNormalizationProjection_f k A M n)
  have hcomp : i.comp ((normalizationProjection k A M).f n).hom =
      ((rawNativeNormalizationProjectorComplex k A M).f n).hom :=
    congrArg (fun f : chainComplex k A M ⟶ chainComplex k A M => (f.f n).hom)
    (normalizationProjection_inverse_eq_rawNativeProjector k A M)
  have h : i.comp p = r :=
    (congrArg (fun f => i.comp f) hp.symm).trans
      (hcomp.trans (rawNativeNormalizationProjectorComplex_f k A M n))
  have hvalue (z : M ⊗[k] TensorPower k n A) :
      i (algebraNormalizationLevelMap k A M n z) = rawNativeNormalizationProjector k A M n z :=
    congrArg (fun f : (M ⊗[k] TensorPower k n A) →ₗ[k] M ⊗[k] TensorPower k n A => f z) h
  calc
    i (a • algebraNormalizationLevelMap k A M n x) = i (algebraNormalizationLevelMap k A M n (a • x)) :=
      congrArg i ((algebraNormalizationLevelMap k A M n).map_smul a x).symm
    _ = rawNativeNormalizationProjector k A M n (a • x) := hvalue (a • x)
    _ = a • rawNativeNormalizationProjector k A M n x := rawNativeNormalizationProjector_smul k A M n a x
    _ = a • i (algebraNormalizationLevelMap k A M n x) := congrArg (fun z => a • z) (hvalue x).symm

/-- The normalized section in the original A-module chain category. -/
def algebraNormalizationInverse : algebraNormalizedChainComplex k A M ⟶ algebraRawComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (algebraNormalizationInverseLevel k A M n)) (by
    intro n
    let i₁ : (M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) →ₗ[k]
        M ⊗[k] TensorPower k (n + 1) A :=
      ((normalizationHomotopyEquiv k A M).inv.f (n + 1)).hom
    let i₀ : (M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) →ₗ[k]
        M ⊗[k] TensorPower k n A := ((normalizationHomotopyEquiv k A M).inv.f n).hom
    let b : (M ⊗[k] TensorPower k (n + 1) A) →ₗ[k] M ⊗[k] TensorPower k n A :=
      ((chainComplex k A M).d (n + 1) n).hom
    let d : (M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) →ₗ[k]
        M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) :=
      ((normalizedChainComplex k A M).d (n + 1) n).hom
    have h : b.comp i₁ = i₀.comp d :=
      congrArg ModuleCat.Hom.hom ((normalizationHomotopyEquiv k A M).inv.comm (n + 1) n)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let z : M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) := x
    dsimp only [algebraRawComplex, algebraNormalizedChainComplex]
    rw [ChainComplex.of_d, ChainComplex.of_d]
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    change b (i₁ z) = i₀ (d z)
    exact congrArg (fun f : (M ⊗[k] TensorPower k (n + 1)
      (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) →ₗ[k] M ⊗[k] TensorPower k n A => f z) h)

/-- The A-linear inverse has the original exact normalization right-inverse law. -/
@[reassoc]
theorem algebraNormalizationInverse_projection :
    algebraNormalizationInverse k A M ≫ algebraNormalizationProjection k A M =
      𝟙 (algebraNormalizedChainComplex k A M) := by
  apply HomologicalComplex.hom_ext
  intro n
  let i : (M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) →ₗ[k]
      M ⊗[k] TensorPower k n A := ((normalizationHomotopyEquiv k A M).inv.f n).hom
  let p := (algebraNormalizationLevelMap k A M n).restrictScalars k
  have hp : ((normalizationProjection k A M).f n).hom = p :=
    congrArg ModuleCat.Hom.hom (nativeNormalizationProjection_f k A M n)
  have hcomp : ((normalizationProjection k A M).f n).hom.comp i = LinearMap.id :=
    congrArg (fun f : normalizedChainComplex k A M ⟶ normalizedChainComplex k A M => (f.f n).hom)
      (normalizationHomotopyEquiv_inv_hom k A M)
  have h : p.comp i = LinearMap.id := (congrArg (fun f => f.comp i) hp.symm).trans hcomp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let z : M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) := x
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp, ModuleCat.hom_id,
    LinearMap.comp_apply, LinearMap.id_apply]
  change p (i z) = z
  exact congrArg (fun f : (M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) →ₗ[k]
    M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) => f z) h

/-- The A-linear projection followed by its native inverse is the raw projector. -/
theorem algebraNormalizationProjection_inverse :
    algebraNormalizationProjection k A M ≫ algebraNormalizationInverse k A M =
      algebraRawNativeNormalizationProjector k A M := by
  apply HomologicalComplex.hom_ext
  intro n
  let i : (M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) →ₗ[k]
      M ⊗[k] TensorPower k n A := ((normalizationHomotopyEquiv k A M).inv.f n).hom
  let p := (algebraNormalizationLevelMap k A M n).restrictScalars k
  let r := rawNativeNormalizationProjector k A M n
  have hp : ((normalizationProjection k A M).f n).hom = p :=
    congrArg ModuleCat.Hom.hom (nativeNormalizationProjection_f k A M n)
  have hcomp : i.comp ((normalizationProjection k A M).f n).hom =
      ((rawNativeNormalizationProjectorComplex k A M).f n).hom :=
    congrArg (fun f : chainComplex k A M ⟶ chainComplex k A M => (f.f n).hom)
      (normalizationProjection_inverse_eq_rawNativeProjector k A M)
  have h : i.comp p = r := (congrArg (fun f => i.comp f) hp.symm).trans
    (hcomp.trans (rawNativeNormalizationProjectorComplex_f k A M n))
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let z : M ⊗[k] TensorPower k n A := x
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  change i (p z) = r z
  exact congrArg (fun f : (M ⊗[k] TensorPower k n A) →ₗ[k] M ⊗[k] TensorPower k n A => f z) h

/-- The original homotopy component, with its A-linearity. -/
def algebraNormalizationHomotopyComponent (n m : ℕ) :
    M ⊗[k] TensorPower k n A →ₗ[A] M ⊗[k] TensorPower k m A where
  toFun := rawNativeNormalizationHomotopyComponent k A M n m
  map_add' x y := map_add _ x y
  map_smul' a x := rawNativeNormalizationHomotopyComponent_smul k A M n m a x

/-- The A-linear raw differential has the same value as the original k-linear differential. -/
theorem algebraRawComplex_d_apply (i j : ℕ) (x : M ⊗[k] TensorPower k i A) :
    ((algebraRawComplex k A M).d i j).hom x = ((chainComplex k A M).d i j).hom x := by
  by_cases hij : i = j + 1
  · subst i
    dsimp only [algebraRawComplex]
    rw [ChainComplex.of_d]
    rfl
  · have hrel : ¬ (ComplexShape.down ℕ).Rel i j := by
      change ¬ (j + 1 = i)
      exact Ne.symm hij
    rw [(algebraRawComplex k A M).shape i j hrel, (chainComplex k A M).shape i j hrel]
    rfl

/-- The normalization homotopy in the original A-module chain category. -/
def algebraRawNativeNormalizationHomotopy :
    Homotopy (algebraRawNativeNormalizationProjector k A M) (𝟙 (algebraRawComplex k A M)) where
  hom n m := ModuleCat.ofHom (algebraNormalizationHomotopyComponent k A M n m)
  zero n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx := ConcreteCategory.congr_hom ((rawNativeNormalizationHomotopy k A M).zero n m h) x
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, rawNativeNormalizationHomotopy_hom] at hx
    change rawNativeNormalizationHomotopyComponent k A M n m x = 0
    exact hx
  comm n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let z : M ⊗[k] TensorPower k n A := x
    let d : ∀ i j, (M ⊗[k] TensorPower k i A) →ₗ[A] M ⊗[k] TensorPower k j A :=
      fun i j => ((algebraRawComplex k A M).d i j).hom
    let b : ∀ i j, (M ⊗[k] TensorPower k i A) →ₗ[k] M ⊗[k] TensorPower k j A :=
      fun i j => ((chainComplex k A M).d i j).hom
    let y₁ : M ⊗[k] TensorPower k n A :=
      rawNativeNormalizationHomotopyComponent k A M ((ComplexShape.down ℕ).next n) n
        (d n ((ComplexShape.down ℕ).next n) z)
    let y₂ : M ⊗[k] TensorPower k n A :=
      d ((ComplexShape.down ℕ).prev n) n
        (rawNativeNormalizationHomotopyComponent k A M n ((ComplexShape.down ℕ).prev n) z)
    have hx := ConcreteCategory.congr_hom ((rawNativeNormalizationHomotopy k A M).comm n) z
    dsimp only [dNext, prevD, AddMonoidHom.mk'] at hx
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hx
    simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
      HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply,
      rawNativeNormalizationProjectorComplex_f, rawNativeNormalizationHomotopy_hom,
      ModuleCat.hom_ofHom] at hx
    change rawNativeNormalizationProjector k A M n z = (y₁ + y₂) + z
    have hd (i j : ℕ) (z : M ⊗[k] TensorPower k i A) : d i j z = b i j z :=
      algebraRawComplex_d_apply k A M i j z
    have hy₁ : y₁ = rawNativeNormalizationHomotopyComponent k A M ((ComplexShape.down ℕ).next n) n
        (b n ((ComplexShape.down ℕ).next n) z) :=
      congrArg (rawNativeNormalizationHomotopyComponent k A M ((ComplexShape.down ℕ).next n) n)
        (hd n ((ComplexShape.down ℕ).next n) z)
    have hy₂ : y₂ = b ((ComplexShape.down ℕ).prev n) n
        (rawNativeNormalizationHomotopyComponent k A M n ((ComplexShape.down ℕ).prev n) z) :=
      hd ((ComplexShape.down ℕ).prev n) n
        (rawNativeNormalizationHomotopyComponent k A M n ((ComplexShape.down ℕ).prev n) z)
    rw [hy₁, hy₂]
    change rawNativeNormalizationProjector k A M n z =
      rawNativeNormalizationHomotopyComponent k A M ((ComplexShape.down ℕ).next n) n
          (b n ((ComplexShape.down ℕ).next n) z) +
        b ((ComplexShape.down ℕ).prev n) n
          (rawNativeNormalizationHomotopyComponent k A M n ((ComplexShape.down ℕ).prev n) z) + z at hx
    exact hx

/-- The original A-linear normalization map has a native A-linear homotopy equivalence. -/
def algebraNormalizationHomotopyEquiv :
    HomotopyEquiv (algebraRawComplex k A M) (algebraNormalizedChainComplex k A M) where
  hom := algebraNormalizationProjection k A M
  inv := algebraNormalizationInverse k A M
  homotopyHomInvId := (Homotopy.ofEq (algebraNormalizationProjection_inverse k A M)).trans
    (algebraRawNativeNormalizationHomotopy k A M)
  homotopyInvHomId := Homotopy.ofEq (algebraNormalizationInverse_projection k A M)

/-- The equivalence retains the original A-linear normalization as its forward map. -/
theorem algebraNormalizationHomotopyEquiv_hom :
    (algebraNormalizationHomotopyEquiv k A M).hom = algebraNormalizationProjection k A M := rfl

/-- The equivalence retains the original A-linear section as its inverse map. -/
theorem algebraNormalizationHomotopyEquiv_inv :
    (algebraNormalizationHomotopyEquiv k A M).inv = algebraNormalizationInverse k A M := rfl

/-- The original A-linear full normalization is a quasi-isomorphism by its homotopy equivalence. -/
instance algebraNormalizationProjection_quasiIso :
    _root_.QuasiIso (algebraNormalizationProjection k A M) :=
  (algebraNormalizationHomotopyEquiv k A M).quasiIso_hom

/-- Restricting the A-linear native homotopy contracts the original categorical normalization kernel. -/
def algebraNormalizationKernelContraction :
    Homotopy (𝟙 (kernel (algebraNormalizationProjection k A M))) 0 :=
  HomologicalComplex.splitHomotopyKernelContraction
    (algebraNormalizationProjection k A M) (algebraNormalizationInverse k A M)
    (algebraNormalizationInverse_projection k A M)
    (algebraNormalizationHomotopyEquiv k A M).homotopyHomInvId

/-- The full normalization kernel is contractible as an A-module chain complex. -/
theorem algebraNormalizationKernel_contractible :
    Nonempty (Homotopy (𝟙 (kernel (algebraNormalizationProjection k A M))) 0) :=
  HomologicalComplex.splitHomotopyKernel_contractible
    (algebraNormalizationProjection k A M) (algebraNormalizationInverse k A M)
    (algebraNormalizationInverse_projection k A M)
    (algebraNormalizationHomotopyEquiv k A M).homotopyHomInvId

/-- Every original homology degree of the full A-linear normalization kernel vanishes. -/
theorem algebraNormalizationKernel_acyclic :
    (kernel (algebraNormalizationProjection k A M)).Acyclic :=
  HomologicalComplex.splitHomotopyKernel_acyclic
    (algebraNormalizationProjection k A M) (algebraNormalizationInverse k A M)
    (algebraNormalizationInverse_projection k A M)
    (algebraNormalizationHomotopyEquiv k A M).homotopyHomInvId

/-- The original regular full normalized complex is placed in the same canonical Hom_A universe. -/
def regularAlgebraNormalizedForHom : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  ((ModuleCat.uliftFunctor.{w, max u v} A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (algebraNormalizedChainComplex k A A)

/-- Native whole-module lifting retains the A-linear normalization homotopy equivalence. -/
def regularAlgebraNormalizationForHom :
    HomotopyEquiv (regularAlgebraRawForHom.{u, v, w} k A)
      (regularAlgebraNormalizedForHom.{u, v, w} k A) :=
  (ModuleCat.uliftFunctor.{w, max u v} A).mapHomotopyEquiv (algebraNormalizationHomotopyEquiv k A A)

/-- Conventional native Hom_A of the original regular normalized full chain complex. -/
def nativeNormalizedAlgebraCochainComplex : CochainComplex (ModuleCat.{max u v w} A) ℕ :=
  (HomologicalComplex.linearHomCochainComplexFunctor A (ModuleCat.{max u v w} A)
    (ModuleCat.of A (ULift.{max u v} M))).obj
      (Opposite.op (regularAlgebraNormalizedForHom.{u, v, w} k A))

/-- Actual A-linear normalization gives Hom_A homotopy invariance for arbitrary original targets. -/
def normalizedAlgebraCochainHomotopyEquiv :
    HomotopyEquiv (nativeNormalizedAlgebraCochainComplex k A M)
      (nativeRawAlgebraCochainComplex k A M) :=
  HomologicalComplex.HomotopyEquiv.mapLinearHomCochainComplex A
    (regularAlgebraNormalizationForHom.{u, v, w} k A)
    (ModuleCat.of A (ULift.{max u v} M))

omit [Module k M] [SMulCommClass k A M] [IsScalarTower k A M] in
/-- The Hom_A forward map is precomposition by the lifted original A-linear normalization. -/
theorem normalizedAlgebraCochainHomotopyEquiv_hom :
    (normalizedAlgebraCochainHomotopyEquiv k A M).hom =
      (HomologicalComplex.linearHomCochainComplexFunctor A (ModuleCat.{max u v w} A)
        (ModuleCat.of A (ULift.{max u v} M))).map
          (((ModuleCat.uliftFunctor.{w, max u v} A).mapHomologicalComplex
            (ComplexShape.down ℕ)).map (algebraNormalizationProjection k A A)).op := rfl

omit [Module k M] [SMulCommClass k A M] [IsScalarTower k A M] in
/-- Each Hom_A cochain is evaluated by precomposition with the original normalized representative map. -/
theorem normalizedAlgebraCochainHomotopyEquiv_hom_f_apply (n : ℕ)
    (φ : (nativeNormalizedAlgebraCochainComplex k A M).X n) :
    (((normalizedAlgebraCochainHomotopyEquiv k A M).hom.f n).hom φ) =
      ((((ModuleCat.uliftFunctor.{w, max u v} A).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (algebraNormalizationProjection k A A)).f n) ≫ φ := rfl

/-- The original normalization-induced Hom_A map gives the all-degree full cohomology comparison. -/
def normalizedAlgebraCohomologyIso (n : ℕ) :
    (nativeNormalizedAlgebraCochainComplex k A M).homology n ≅
      (nativeRawAlgebraCochainComplex k A M).homology n :=
  (normalizedAlgebraCochainHomotopyEquiv k A M).toHomologyIso n

omit [Module k M] [SMulCommClass k A M] [IsScalarTower k A M] in
/-- The full cohomology isomorphism keeps the normalization-induced Hom_A homology map as its forward map. -/
theorem normalizedAlgebraCohomologyIso_hom (n : ℕ) :
    (normalizedAlgebraCohomologyIso k A M n).hom =
      HomologicalComplex.homologyMap (normalizedAlgebraCochainHomotopyEquiv k A M).hom n := rfl

/-- The full Hom_A normalization comparison is natural in the original A-module coefficient object. -/
def normalizedAlgebraCohomologyNatIso (n : ℕ) :
    HomologicalComplex.linearHomCochainComplexHomologyFunctor A (ModuleCat.{max u v w} A)
        (regularAlgebraNormalizedForHom.{u, v, w} k A) n ≅
      HomologicalComplex.linearHomCochainComplexHomologyFunctor A (ModuleCat.{max u v w} A)
        (regularAlgebraRawForHom.{u, v, w} k A) n :=
  HomologicalComplex.HomotopyEquiv.linearHomCochainComplexHomologyNatIso A
    (regularAlgebraNormalizationForHom.{u, v, w} k A) n

end ModuleCat.Algebra.Hochschild.Symmetric
