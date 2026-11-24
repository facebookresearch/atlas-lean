/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Cyclic
public import MathlibExt.LinearAlgebra.TensorPower.Cons
public import Mathlib.Algebra.Homology.Homotopy

import Mathlib.Tactic.Abel

/-!
# extra degeneracy and Connes boundary on the regular tensor levels

Insertion uses an vector in the original first-factor coordinates. A
left unit earns the omitted-face contraction; a ring chooses its original unit.
Connes B is N followed by that insertion and 1-t. Native homotopy composition
supplies its mixed law, and the (1-t)N identity supplies its square.
All contractions are in the original ground modules.

The definition is Loday 2.1.7.1. The second-family minus printed in 2.1.7.3
contradicts the same page's low-degree values and is not asserted here.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite AlgebraicTopology
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k]

section General

variable (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- Insert the vector before the original coefficient and tensor tail. -/
def extraDegeneracyWith (e : A) (n : ℕ) :
    chainLevel k A A n ⟶ chainLevel k A A (n + 1) :=
  ModuleCat.ofHom (TensorPower.consInsert k A e n)

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Insertion retains the original first coefficient and every tail factor. -/
@[simp]
theorem extraDegeneracyWith_tprod (e : A) (n : ℕ) (m : A) (a : Fin n → A) :
    (extraDegeneracyWith k A e n).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      e ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons m a) :=
  TensorPower.consInsert_tmul k A e n m a

/-- An left unit contracts the original first face. -/
theorem extraDegeneracyWith_first (e : A) (hLeft : ∀ a : A, e * a = a) (n : ℕ) :
    extraDegeneracyWith k A e n ≫ regularFace k A n 0 = 𝟙 (chainLevel k A A n) := by
  apply ModuleCat.hom_ext
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
    LinearMap.id_apply]
  erw [extraDegeneracyWith_tprod, regularFace_first_tprod]
  change (e * m) ⊗ₜ[k] PiTensorProduct.tprod k a = m ⊗ₜ[k] PiTensorProduct.tprod k a
  rw [hLeft m]

/-- Shifted retained faces commute with inserting any vector. -/
theorem extraDegeneracyWith_shift (e : A) (n : ℕ) (i : Fin (n + 1)) :
    extraDegeneracyWith k A e (n + 1) ≫ regularFace k A (n + 1) i.succ.castSucc =
      regularFace k A n i.castSucc ≫ extraDegeneracyWith k A e n := by
  apply ModuleCat.hom_ext
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [extraDegeneracyWith_tprod, ← Fin.succ_castSucc, regularFace_inner_tprod]
  cases i using Fin.cases with
  | zero =>
    erw [regularFace_first_tprod, extraDegeneracyWith_tprod, mulAdjacent_cons_zero]
  | succ i =>
    erw [← Fin.succ_castSucc, regularFace_inner_tprod,
      extraDegeneracyWith_tprod, mulAdjacent_cons_succ]

/-- The left-unit insertion contracts the selected b-prime complex, including X0. -/
def bPrimeContractionOfLeftUnit (e : A) (hLeft : ∀ a : A, e * a = a) :
    Homotopy (𝟙 (bPrimeComplex k A)) 0 :=
  TruncatedAlternatingFaceMapComplex.contractingHomotopy (regularBar k A)
    (extraDegeneracyWith k A e)
    (fun j => by
      change extraDegeneracyWith k A e j ≫ (regularBar k A).δ (0 : Fin (j + 2)) =
        𝟙 (chainLevel k A A j)
      erw [ModuleCat.Algebra.Hochschild.NonUnital.bar_δ]
      exact extraDegeneracyWith_first k A e hLeft j)
    (fun j i => by
      change extraDegeneracyWith k A e (j + 1) ≫ (regularBar k A).δ i.succ.castSucc =
        (regularBar k A).δ i.castSucc ≫ extraDegeneracyWith k A e j
      erw [ModuleCat.Algebra.Hochschild.NonUnital.bar_δ,
        ModuleCat.Algebra.Hochschild.NonUnital.bar_δ]
      exact extraDegeneracyWith_shift k A e j i)

/-- The contraction has the same unit-insertion component. -/
@[simp]
theorem bPrimeContractionOfLeftUnit_hom (e : A) (hLeft : ∀ a : A, e * a = a) (n : ℕ) :
    (bPrimeContractionOfLeftUnit k A e hLeft).hom n (n + 1) =
      extraDegeneracyWith k A e n := by
  unfold bPrimeContractionOfLeftUnit
  exact TruncatedAlternatingFaceMapComplex.contractingHomotopy_hom (regularBar k A)
    (extraDegeneracyWith k A e)
    (fun j => by
      change extraDegeneracyWith k A e j ≫ (regularBar k A).δ (0 : Fin (j + 2)) =
        𝟙 (chainLevel k A A j)
      erw [ModuleCat.Algebra.Hochschild.NonUnital.bar_δ]
      exact extraDegeneracyWith_first k A e hLeft j)
    (fun j i => by
      change extraDegeneracyWith k A e (j + 1) ≫ (regularBar k A).δ i.succ.castSucc =
        (regularBar k A).δ i.castSucc ≫ extraDegeneracyWith k A e j
      erw [ModuleCat.Algebra.Hochschild.NonUnital.bar_δ,
        ModuleCat.Algebra.Hochschild.NonUnital.bar_δ]
      exact extraDegeneracyWith_shift k A e j i) n

/-- The secondary operator uses the original norm, insertion and 1-t. -/
def connesBoundaryWith (e : A) (n : ℕ) :
    chainLevel k A A n ⟶ chainLevel k A A (n + 1) :=
  normMap k A n ≫ extraDegeneracyWith k A e n ≫
    (𝟙 (chainLevel k A A (n + 1)) - cyclicMap k A (n + 1))

/-- The left-unit contraction gives the native zero-to-zero homotopy with Connes components. -/
def connesBoundaryHomotopyOfLeftUnit (e : A) (hLeft : ∀ a : A, e * a = a) :
    Homotopy (0 : bComplex k A ⟶ bComplex k A) 0 := by
  let H := ((bPrimeContractionOfLeftUnit k A e hLeft).compLeft
    (normChainMap k A)).compRight (oneSubCyclicChainMap k A)
  have h₁ : (normChainMap k A ≫ 𝟙 (bPrimeComplex k A)) ≫
      oneSubCyclicChainMap k A = 0 := by
    rw [Category.comp_id, normChainMap_comp_oneSubCyclicChainMap]
  have h₂ : (normChainMap k A ≫ (0 : bPrimeComplex k A ⟶ bPrimeComplex k A)) ≫
      oneSubCyclicChainMap k A = 0 := by
    rw [comp_zero, zero_comp]
  exact (Homotopy.ofEq h₁.symm).trans (H.trans (Homotopy.ofEq h₂))

/-- The native secondary homotopy has precisely the N then s then 1-t component. -/
@[simp]
theorem connesBoundaryHomotopyOfLeftUnit_hom (e : A) (hLeft : ∀ a : A, e * a = a)
    (n : ℕ) :
    (connesBoundaryHomotopyOfLeftUnit k A e hLeft).hom n (n + 1) =
      connesBoundaryWith k A e n := by
  dsimp only [connesBoundaryHomotopyOfLeftUnit, Homotopy.trans, Homotopy.ofEq,
    Homotopy.compLeft, Homotopy.compRight]
  simp only [Pi.add_apply, Pi.zero_apply, zero_add, add_zero,
    bPrimeContractionOfLeftUnit_hom, normChainMap_f, oneSubCyclicChainMap_f,
    connesBoundaryWith]
  exact Category.assoc (normMap k A n) (extraDegeneracyWith k A e n)
    (𝟙 (chainLevel k A A (n + 1)) - cyclicMap k A (n + 1))

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- The central (1-t)N zero composite makes the B square zero for any vector. -/
theorem connesBoundaryWith_square (e : A) (n : ℕ) :
    connesBoundaryWith k A e n ≫ connesBoundaryWith k A e (n + 1) = 0 := by
  calc
    _ = normMap k A n ≫ extraDegeneracyWith k A e n ≫
        ((𝟙 (chainLevel k A A (n + 1)) - cyclicMap k A (n + 1)) ≫ normMap k A (n + 1)) ≫
          extraDegeneracyWith k A e (n + 1) ≫
            (𝟙 (chainLevel k A A (n + 2)) - cyclicMap k A (n + 2)) := by
      simp only [connesBoundaryWith, Category.assoc]
    _ = 0 := by
      rw [oneSubCyclicMap_comp_normMap]
      simp only [zero_comp, comp_zero]

/-- Native homotopy commutation gives the mixed law in every successor degree. -/
theorem connesBoundaryWith_mixed (e : A) (hLeft : ∀ a : A, e * a = a) (n : ℕ) :
    let d₀ : chainLevel k A A (n + 1) ⟶ chainLevel k A A n :=
      (bComplex k A).d (n + 1) n
    let d₁ : chainLevel k A A (n + 2) ⟶ chainLevel k A A (n + 1) :=
      (bComplex k A).d (n + 2) (n + 1)
    connesBoundaryWith k A e (n + 1) ≫ d₁ + d₀ ≫ connesBoundaryWith k A e n = 0 := by
  let K := bComplex k A
  let H : Homotopy (0 : K ⟶ K) 0 := connesBoundaryHomotopyOfLeftUnit k A e hLeft
  let β₀ : K.X n ⟶ K.X (n + 1) := connesBoundaryWith k A e n
  let β₁ : K.X (n + 1) ⟶ K.X (n + 2) := connesBoundaryWith k A e (n + 1)
  let d₀ : K.X (n + 1) ⟶ K.X n := K.d (n + 1) n
  let d₁ : K.X (n + 2) ⟶ K.X (n + 1) := K.d (n + 2) (n + 1)
  have hβ₀ : H.hom n (n + 1) = β₀ :=
    connesBoundaryHomotopyOfLeftUnit_hom k A e hLeft n
  have hβ₁ : H.hom (n + 1) (n + 2) = β₁ :=
    connesBoundaryHomotopyOfLeftUnit_hom k A e hLeft (n + 1)
  have hc : 0 = d₀ ≫ H.hom n (n + 1) + H.hom (n + 1) (n + 2) ≫ d₁ := by
    have h := H.comm (n + 1)
    rw [HomologicalComplex.zero_f_apply, add_zero,
      dNext_eq H.hom (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n),
      prevD_eq H.hom (by rfl : (ComplexShape.down ℕ).Rel (n + 2) (n + 1))] at h
    exact h
  have hs : d₀ ≫ H.hom n (n + 1) + H.hom (n + 1) (n + 2) ≫ d₁ =
      d₀ ≫ β₀ + β₁ ≫ d₁ :=
    congrArg₂ (fun (a : K.X n ⟶ K.X (n + 1))
      (b : K.X (n + 1) ⟶ K.X (n + 2)) => d₀ ≫ a + b ≫ d₁) hβ₀ hβ₁
  change β₁ ≫ d₁ + d₀ ≫ β₀ = 0
  exact (add_comm _ _).trans (hc.trans hs).symm

/-- The same native homotopy retains the bottom mixed identity at the original X0. -/
theorem connesBoundaryWith_comp_d_zero (e : A) (hLeft : ∀ a : A, e * a = a) :
    connesBoundaryWith k A e 0 ≫ (bComplex k A).d 1 0 = 0 := by
  let K := bComplex k A
  let H : Homotopy (0 : K ⟶ K) 0 := connesBoundaryHomotopyOfLeftUnit k A e hLeft
  let β : K.X 0 ⟶ K.X 1 := connesBoundaryWith k A e 0
  let d : K.X 1 ⟶ K.X 0 := K.d 1 0
  have hβ : H.hom 0 1 = β := connesBoundaryHomotopyOfLeftUnit_hom k A e hLeft 0
  have hc : 0 = H.hom 0 1 ≫ d := by
    have h := H.comm 0
    rw [HomologicalComplex.zero_f_apply, add_zero,
      dNext_eq_zero H.hom 0 (by simp [ComplexShape.down_Rel]),
      prevD_eq H.hom (by rfl : (ComplexShape.down ℕ).Rel 1 0), zero_add] at h
    exact h
  change β ≫ d = 0
  exact (hc.trans (congrArg (fun a : K.X 0 ⟶ K.X 1 => a ≫ d) hβ)).symm


omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- The secondary operator applies the original norm, insertion, and signed difference. -/
theorem connesBoundaryWith_apply (e : A) (n : ℕ) (x : chainLevel k A A n) :
    (connesBoundaryWith k A e n).hom x =
      (extraDegeneracyWith k A e n).hom (TensorPower.consNorm k A n x) -
        TensorPower.consCyclicOperator k A (n + 1)
          ((extraDegeneracyWith k A e n).hom (TensorPower.consNorm k A n x)) := rfl

section Naturality

variable {k A} {B : Type w} [NonUnitalRing B] [Module k B]

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Original arbitrary linear maps take the insertion vector to its image. -/
theorem extraDegeneracyWith_naturality (f : A →ₗ[k] B) (e : A) (n : ℕ) :
    (TensorPower.consLevelMap f (n + 1)).comp (extraDegeneracyWith k A e n).hom =
      (extraDegeneracyWith k B (f e) n).hom.comp (TensorPower.consLevelMap f n) :=
  TensorPower.consInsert_naturality f e n

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Connes data is natural under original linear maps and their insertion vectors. -/
theorem connesBoundaryWith_naturality (f : A →ₗ[k] B) (e : A) (n : ℕ) :
    (TensorPower.consLevelMap f (n + 1)).comp (connesBoundaryWith k A e n).hom =
      (connesBoundaryWith k B (f e) n).hom.comp (TensorPower.consLevelMap f n) := by
  let TA := fun r => A ⊗[k] TensorPower k r A
  let TB := fun r => B ⊗[k] TensorPower k r B
  let F := fun r => (TensorPower.consLevelMap f r : TA r →ₗ[k] TB r)
  let NA : Module.End k (TA n) := TensorPower.consNorm k A n
  let NB : Module.End k (TB n) := TensorPower.consNorm k B n
  let tA : Module.End k (TA (n + 1)) := TensorPower.consCyclicOperator k A (n + 1)
  let tB : Module.End k (TB (n + 1)) := TensorPower.consCyclicOperator k B (n + 1)
  let sA : TA n →ₗ[k] TA (n + 1) := (extraDegeneracyWith k A e n).hom
  let sB : TB n →ₗ[k] TB (n + 1) := (extraDegeneracyWith k B (f e) n).hom
  let BA : TA n →ₗ[k] TA (n + 1) := (connesBoundaryWith k A e n).hom
  let BB : TB n →ₗ[k] TB (n + 1) := (connesBoundaryWith k B (f e) n).hom
  have hBA (x : TA n) : BA x = sA (NA x) - tA (sA (NA x)) :=
    connesBoundaryWith_apply k A e n x
  have hBB (x : TB n) : BB x = sB (NB x) - tB (sB (NB x)) :=
    rfl
  apply LinearMap.ext
  intro x
  change F (n + 1) (BA x) = BB (F n x)
  have hN : F n (NA x) = NB (F n x) := TensorPower.consNorm_natural f n x
  have hS₀ : F (n + 1) (sA (NA x)) = sB (F n (NA x)) :=
    DFunLike.congr_fun (extraDegeneracyWith_naturality f e n) (NA x)
  have hS : F (n + 1) (sA (NA x)) = sB (NB (F n x)) :=
    hS₀.trans (congrArg sB hN)
  have hC : F (n + 1) (tA (sA (NA x))) = tB (F (n + 1) (sA (NA x))) :=
    DFunLike.congr_fun (TensorPower.consCyclicOperator_natural f (n + 1)) (sA (NA x))
  calc
    _ = F (n + 1) (sA (NA x) - tA (sA (NA x))) := congrArg (F (n + 1)) (hBA x)
    _ = F (n + 1) (sA (NA x)) - F (n + 1) (tA (sA (NA x))) := map_sub _ _ _
    _ = sB (NB (F n x)) - tB (sB (NB (F n x))) :=
      congrArg₂ (fun a b : TB (n + 1) => a - b) hS (hC.trans (congrArg tB hS))
    _ = BB (F n x) := (hBB (F n x)).symm

end Naturality


omit [IsScalarTower k A A] [SMulCommClass k A A] in
theorem consCyclic_pair_value (a b : A) :
    TensorPower.consCyclicOperator k A 1
        (a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => b)) =
      -(b ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => a)) := by
  let v : Fin 2 → A := Fin.cons a (fun _ : Fin 1 => b)
  have hi : (fun i : Fin 1 => v i.castSucc) = (fun _ : Fin 1 => a) := by
    funext i
    have h : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have h := TensorPower.consCyclicOperator_tmul k A 1 v
  change TensorPower.consCyclicOperator k A 1
      (a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => b)) =
    (-1 : k) ^ 1 • (b ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin 1 => v i.castSucc)) at h
  rw [hi] at h
  simpa only [pow_one, neg_one_smul] using h

omit [IsScalarTower k A A] [SMulCommClass k A A] in
theorem consCyclic_triple_value (a b c : A) :
    TensorPower.consCyclicOperator k A 2
        (a ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons b (fun _ : Fin 1 => c))) =
      c ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons a (fun _ : Fin 1 => b)) := by
  let v : Fin 3 → A := Fin.cons a (Fin.cons b (fun _ : Fin 1 => c))
  have hi : (fun i : Fin 2 => v i.castSucc) = Fin.cons a (fun _ : Fin 1 => b) := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      have h : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
  have h := TensorPower.consCyclicOperator_tmul k A 2 v
  change TensorPower.consCyclicOperator k A 2
      (a ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons b (fun _ : Fin 1 => c))) =
    (-1 : k) ^ 2 • (c ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin 2 => v i.castSucc)) at h
  rw [hi] at h
  simpa only [pow_two, neg_mul_neg, one_mul, one_smul] using h

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Degree zero of the 2.1.7.1 operator has the verified plus sign. -/
theorem connesBoundaryWith_zero_tprod (e a : A) :
    (connesBoundaryWith k A e 0).hom
        (a ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin 0 => Fin.elim0 i)) =
      e ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => a) +
        a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => e) := by
  have hn : TensorPower.consNorm k A 0
      (a ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin 0 => Fin.elim0 i)) =
      a ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin 0 => Fin.elim0 i) := by
    rw [TensorPower.consNorm_zero]
    rfl
  have hi : Fin.cons a (fun i : Fin 0 => Fin.elim0 i) = (fun _ : Fin 1 => a) := by
    funext i
    have h : (i : Fin 1) = (0 : Fin 1) := by
      apply Fin.ext
      omega
    subst i
    rfl
  have hs : (extraDegeneracyWith k A e 0).hom
      (a ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin 0 => Fin.elim0 i)) =
      e ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => a) := by
    simpa only [hi] using
      extraDegeneracyWith_tprod k A e 0 a (fun i : Fin 0 => Fin.elim0 i)
  rw [connesBoundaryWith_apply, hn, hs, consCyclic_pair_value, sub_neg_eq_add]

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Degree one has both verified pairs of terms on the original tensor levels. -/
theorem connesBoundaryWith_one_tprod (e a b : A) :
    (connesBoundaryWith k A e 1).hom
        (a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => b)) =
      e ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons a (fun _ : Fin 1 => b)) -
        e ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons b (fun _ : Fin 1 => a)) +
          a ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons e (fun _ : Fin 1 => b)) -
            b ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons e (fun _ : Fin 1 => a)) := by
  have hn : TensorPower.consNorm k A 1 = 1 + TensorPower.consCyclicOperator k A 1 := by
    simp only [TensorPower.consNorm_eq_sum, Finset.sum_range_succ,
      Finset.sum_range_zero, pow_zero, pow_one, zero_add]
  have hv : TensorPower.consNorm k A 1
      (a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => b)) =
      a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => b) -
        b ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => a) := by
    rw [hn]
    change (a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => b)) +
      TensorPower.consCyclicOperator k A 1
        (a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => b)) = _
    rw [consCyclic_pair_value]
    rfl
  change @Eq (A ⊗[k] TensorPower k 2 A)
    (TensorPower.consInsert k A e 1
        (TensorPower.consNorm k A 1
          (a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => b))) -
      TensorPower.consCyclicOperator k A 2
        (TensorPower.consInsert k A e 1
          (TensorPower.consNorm k A 1
            (a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => b)))))
    (e ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons a (fun _ : Fin 1 => b)) -
      e ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons b (fun _ : Fin 1 => a)) +
        a ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons e (fun _ : Fin 1 => b)) -
          b ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons e (fun _ : Fin 1 => a)))
  have ht₁ := consCyclic_triple_value k A e a b
  have ht₂ := consCyclic_triple_value k A e b a
  simp only [hv, map_sub, TensorPower.consInsert_tmul]
  erw [ht₁, ht₂]
  abel

end General

section Unital

variable (A : Type v) [Ring A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The ordinary extra degeneracy chooses the algebra's unit. -/
abbrev extraDegeneracy (n : ℕ) : chainLevel k A A n ⟶ chainLevel k A A (n + 1) :=
  extraDegeneracyWith k A 1 n

/-- The original unit earns the native b-prime contraction. -/
def bPrimeContraction : Homotopy (𝟙 (bPrimeComplex k A)) 0 :=
  bPrimeContractionOfLeftUnit k A 1 (fun a => one_mul a)

/-- The standard contraction's component is the original unit insertion. -/
@[simp]
theorem bPrimeContraction_hom (n : ℕ) :
    (bPrimeContraction k A).hom n (n + 1) = extraDegeneracy k A n :=
  bPrimeContractionOfLeftUnit_hom k A 1 (fun a => one_mul a) n

/-- The unital Connes boundary is N followed by unit insertion and 1-t. -/
def connesBoundary (n : ℕ) : chainLevel k A A n ⟶ chainLevel k A A (n + 1) :=
  connesBoundaryWith k A 1 n

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- The standard boundary has the printed 2.1.7.1 composition on the original levels. -/
theorem connesBoundary_eq (n : ℕ) :
    connesBoundary k A n = normMap k A n ≫ extraDegeneracy k A n ≫
      (𝟙 (chainLevel k A A (n + 1)) - cyclicMap k A (n + 1)) := rfl

/-- The unital Connes components form a native zero-to-zero homotopy. -/
def connesBoundaryHomotopy : Homotopy (0 : bComplex k A ⟶ bComplex k A) 0 :=
  connesBoundaryHomotopyOfLeftUnit k A 1 (fun a => one_mul a)

/-- The packaged zero homotopy retains the unital boundary. -/
@[simp]
theorem connesBoundaryHomotopy_hom (n : ℕ) :
    (connesBoundaryHomotopy k A).hom n (n + 1) = connesBoundary k A n :=
  connesBoundaryHomotopyOfLeftUnit_hom k A 1 (fun a => one_mul a) n

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- The unital Connes boundary squares to zero in every degree. -/
theorem connesBoundary_square (n : ℕ) :
    connesBoundary k A n ≫ connesBoundary k A (n + 1) = 0 :=
  connesBoundaryWith_square k A 1 n

/-- The unital boundary anticommutes with the original Hochschild differential. -/
theorem connesBoundary_mixed (n : ℕ) :
    let d₀ : chainLevel k A A (n + 1) ⟶ chainLevel k A A n :=
      (bComplex k A).d (n + 1) n
    let d₁ : chainLevel k A A (n + 2) ⟶ chainLevel k A A (n + 1) :=
      (bComplex k A).d (n + 2) (n + 1)
    connesBoundary k A (n + 1) ≫ d₁ + d₀ ≫ connesBoundary k A n = 0 :=
  connesBoundaryWith_mixed k A 1 (fun a => one_mul a) n

/-- The original bottom term satisfies the same mixed identity. -/
theorem connesBoundary_comp_d_zero :
    connesBoundary k A 0 ≫ (bComplex k A).d 1 0 = 0 :=
  connesBoundaryWith_comp_d_zero k A 1 (fun a => one_mul a)

section Naturality

variable {k A} {B : Type w} [Ring B] [Module k B]

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Actual unit-preserving maps retain the Connes boundary in independent raw worlds. -/
theorem connesBoundary_naturality (f : A →ₙₐ[k] B) (hOne : f 1 = 1) (n : ℕ) :
    (TensorPower.consLevelMap (f : A →ₗ[k] B) (n + 1)).comp (connesBoundary k A n).hom =
      (connesBoundary k B n).hom.comp (TensorPower.consLevelMap (f : A →ₗ[k] B) n) := by
  have hOneLinear : (f : A →ₗ[k] B) (1 : A) = (1 : B) := by
    change f (1 : A) = (1 : B)
    exact hOne
  simpa only [connesBoundary, hOneLinear] using
    connesBoundaryWith_naturality (f : A →ₗ[k] B) (1 : A) n

end Naturality


omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- The standard unit gives the verified printed degree-zero plus value. -/
theorem connesBoundary_zero_tprod (a : A) :
    (connesBoundary k A 0).hom
        (a ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin 0 => Fin.elim0 i)) =
      1 ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => a) +
        a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => (1 : A)) :=
  connesBoundaryWith_zero_tprod k A 1 a

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- The standard unit gives all four verified degree-one terms. -/
theorem connesBoundary_one_tprod (a b : A) :
    (connesBoundary k A 1).hom
        (a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => b)) =
      1 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons a (fun _ : Fin 1 => b)) -
        1 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons b (fun _ : Fin 1 => a)) +
          a ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons (1 : A) (fun _ : Fin 1 => b)) -
            b ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons (1 : A) (fun _ : Fin 1 => a)) :=
  connesBoundaryWith_one_tprod k A 1 a b

end Unital

end ModuleCat.Algebra.Hochschild.NonUnital
