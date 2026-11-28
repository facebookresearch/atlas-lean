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

/- Source convention note retained from the original discussion: equation 2.1.7.1 defines (1−t)sN.
  The second-family minus recorded in equation 2.1.7.3 is reported there to disagree with that
  composition and its low-degree values. The definitions and value lemmas below use the composition
  convention. -/

/-!
# Unit insertion and the Connes operator

Let k be a commutative ring and A a nonunital associative ring with
k-bilinear multiplication. In C_n(A) = A ⊗[k] A^{⊗n}, inserting e ∈ A
at the front gives s_{e,n}(a_0 ⊗ ⋯ ⊗ a_n) = e ⊗ a_0 ⊗ ⋯ ⊗ a_n.
If e is a left unit, ea = a for all a, these maps contract the b′
complex, including degree zero.

Let t_n be the signed last-to-first rotation and N_n = ∑_{j=0}^{n} t_n^j.
The secondary operator is B_{e,n} = (1 − t_{n+1}) s_{e,n} N_n.
It satisfies B_e² = 0 for every e. With e a left unit it also satisfies
bB_e + B_e b = 0, expressed as a chain homotopy from zero to zero.

For unital A, choose e = 1. Then
B_0(a) = 1 ⊗ a + a ⊗ 1 and
B_1(a ⊗ b) = 1 ⊗ a ⊗ b − 1 ⊗ b ⊗ a
+ a ⊗ 1 ⊗ b − b ⊗ 1 ⊗ a.
The vector-parametrized operators are natural under k-linear maps
when e is sent to its image. The unit-parametrized operators are
natural under multiplicative k-linear maps preserving 1.

Reference: J.-L. Loday, Cyclic Homology, equation 2.1.7.1.
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

/-- Let k be a commutative ring and A a nonunital associative ring
with a k-module structure. Put C_n = A ⊗[k] A^{⊗n}.
For e ∈ A, front insertion is the k-linear map
s_{e,n} : C_n → C_{n+1}, sending a_0 ⊗ ⋯ ⊗ a_n to
e ⊗ a_0 ⊗ ⋯ ⊗ a_n. -/
def extraDegeneracyWith (e : A) (n : ℕ) :
    chainLevel k A A n ⟶ chainLevel k A A (n + 1) :=
  ModuleCat.ofHom (TensorPower.consInsert k A e n)

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Let k be a commutative ring and A a nonunital associative ring
with a k-module structure. Put C_n = A ⊗[k] A^{⊗n}.
For e,m ∈ A and a : Fin n → A, the insertion has value
s_{e,n}(m ⊗ tprod(a)) = e ⊗ tprod(cons(m,a)). -/
@[simp]
theorem extraDegeneracyWith_tprod (e : A) (n : ℕ) (m : A) (a : Fin n → A) :
    (extraDegeneracyWith k A e n).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      e ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons m a) :=
  TensorPower.consInsert_tmul k A e n m a

/-- Let k be a commutative ring and A a nonunital associative ring
with k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}.
If e ∈ A is a left unit, ea = a for every a, then the first
Hochschild face satisfies δ_0 s_{e,n} = id_{C_n}. -/
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

/-- Let k be a commutative ring and A a nonunital associative ring
with k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}.
For every e ∈ A and retained adjacent-face index 0 ≤ i ≤ n,
front insertion satisfies δ_{i+1} s_{e,n+1} = s_{e,n} δ_i
as maps C_{n+1} → C_{n+1}. -/
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

/-- Let k be a commutative ring and A a nonunital associative ring
with k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}.
If ea = a for every a ∈ A, the insertion maps s_{e,n} give a
contracting homotopy of the b′ complex: b′ s_e + s_e b′ = id,
with b′_1 s_{e,0} = id in degree zero. -/
def bPrimeContractionOfLeftUnit (e : A) (hLeft : ∀ a : A, e * a = a) :
    Homotopy (𝟙 (bPrimeComplex k A)) 0 :=
  LastFaceOmittedAlternatingFaceMapComplex.contractingHomotopy (regularBar k A)
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

/-- Let k be a commutative ring and A a nonunital associative ring
with k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}.
For a left unit e, the degree-(n,n+1) component of the
contracting homotopy of the b′ complex is s_{e,n}. -/
@[simp]
theorem bPrimeContractionOfLeftUnit_hom (e : A) (hLeft : ∀ a : A, e * a = a) (n : ℕ) :
    (bPrimeContractionOfLeftUnit k A e hLeft).hom n (n + 1) =
      extraDegeneracyWith k A e n := by
  unfold bPrimeContractionOfLeftUnit
  exact LastFaceOmittedAlternatingFaceMapComplex.contractingHomotopy_hom (regularBar k A)
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

/-- Let k be a commutative ring and A a nonunital associative ring
with a k-module structure. Put C_n = A ⊗[k] A^{⊗n}.
Write s_{e,n}(a_0 ⊗ ⋯ ⊗ a_n) = e ⊗ a_0 ⊗ ⋯ ⊗ a_n,
t_n for the signed last-to-first rotation, and N_n = ∑_{j=0}^{n} t_n^j.
Set B_{e,n} = (1 − t_{n+1}) s_{e,n} N_n.
This defines the k-linear secondary operator C_n → C_{n+1}. -/
def connesBoundaryWith (e : A) (n : ℕ) :
    chainLevel k A A n ⟶ chainLevel k A A (n + 1) :=
  normMap k A n ≫ extraDegeneracyWith k A e n ≫
    (𝟙 (chainLevel k A A (n + 1)) - cyclicMap k A (n + 1))

/-- Let k be a commutative ring and A a nonunital associative ring
with k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}.
If e is a left unit, the operators
B_{e,n} = (1 − t_{n+1}) s_{e,n} N_n form a homotopy from
the zero chain map of C_*(A) to itself, expressing bB_e + B_e b = 0. -/
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

/-- Let k be a commutative ring and A a nonunital associative ring
with k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}.
For a left unit e, the degree-(n,n+1) component of the zero-to-zero
mixed homotopy is exactly B_{e,n} = (1 − t_{n+1}) s_{e,n} N_n. -/
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
/-- Let k be a commutative ring and A a nonunital associative ring
with a k-module structure. Put C_n = A ⊗[k] A^{⊗n}.
Write s_{e,n}(a_0 ⊗ ⋯ ⊗ a_n) = e ⊗ a_0 ⊗ ⋯ ⊗ a_n,
t_n for the signed last-to-first rotation, and N_n = ∑_{j=0}^{n} t_n^j.
Set B_{e,n} = (1 − t_{n+1}) s_{e,n} N_n.
For every e and n, B_{e,n+1} B_{e,n} = 0. The intermediate
factor N_{n+1}(1 − t_{n+1}) vanishes. -/
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

/-- Let k be a commutative ring and A a nonunital associative ring
with k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}.
For a left unit e, the secondary operator satisfies
b_{n+2} B_{e,n+1} + B_{e,n} b_{n+1} = 0
as an endomorphism of C_{n+1}, for every n ≥ 0. -/
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

/-- Let k be a commutative ring and A a nonunital associative ring
with k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}.
For a left unit e, the bottom mixed relation is
b_1 B_{e,0} = 0 as an endomorphism of C_0. -/
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
/-- Let k be a commutative ring and A a nonunital associative ring
with a k-module structure. Put C_n = A ⊗[k] A^{⊗n}.
Write s_{e,n}(a_0 ⊗ ⋯ ⊗ a_n) = e ⊗ a_0 ⊗ ⋯ ⊗ a_n,
t_n for the signed last-to-first rotation, and N_n = ∑_{j=0}^{n} t_n^j.
Set B_{e,n} = (1 − t_{n+1}) s_{e,n} N_n.
On x ∈ C_n, the operator has value
B_{e,n}(x) = s_{e,n}(N_n x) − t_{n+1}(s_{e,n}(N_n x)). -/
theorem connesBoundaryWith_apply (e : A) (n : ℕ) (x : chainLevel k A A n) :
    (connesBoundaryWith k A e n).hom x =
      (extraDegeneracyWith k A e n).hom (TensorPower.consNorm k A n x) -
        TensorPower.consCyclicOperator k A (n + 1)
          ((extraDegeneracyWith k A e n).hom (TensorPower.consNorm k A n x)) := rfl

section Naturality

variable {k A} {B : Type w} [NonUnitalRing B] [Module k B]

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Let k be commutative, A,B nonunital associative rings with k-module
structures, f : A → B k-linear, and e ∈ A. Applying f to every
tensor factor gives F_n, and front insertion is natural:
F_{n+1} s_{e,n} = s_{f(e),n} F_n.
The algebra and target carrier universes are independent. -/
theorem extraDegeneracyWith_naturality (f : A →ₗ[k] B) (e : A) (n : ℕ) :
    (TensorPower.consLevelMap f (n + 1)).comp (extraDegeneracyWith k A e n).hom =
      (extraDegeneracyWith k B (f e) n).hom.comp (TensorPower.consLevelMap f n) :=
  TensorPower.consInsert_naturality f e n

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Let k be commutative, A,B nonunital associative rings with k-module
structures, and f : A → B k-linear. For e ∈ A, the secondary
operators B_e = (1−t)s_e N satisfy
F_{n+1} B_{e,n} = B_{f(e),n} F_n,
where F_n applies f to all n+1 tensor factors. -/
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
/-- Let k be a commutative ring and A a nonunital associative ring
with a k-module structure. Put C_n = A ⊗[k] A^{⊗n}.
For e,a ∈ A, the degree-zero operator has value
B_{e,0}(a) = e ⊗ a + a ⊗ e under the empty-tensor coordinates. -/
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
/-- Let k be a commutative ring and A a nonunital associative ring
with a k-module structure. Put C_n = A ⊗[k] A^{⊗n}.
For e,a,b ∈ A, the degree-one operator has value
B_{e,1}(a ⊗ b) = e ⊗ a ⊗ b − e ⊗ b ⊗ a
+ a ⊗ e ⊗ b − b ⊗ e ⊗ a. -/
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

/-- Let k be commutative and A an associative unital ring with a
k-module structure. Put C_n = A ⊗[k] A^{⊗n}.
The unit extra degeneracy is s_n = s_{1,n}, the front insertion
map a_0 ⊗ ⋯ ⊗ a_n ↦ 1 ⊗ a_0 ⊗ ⋯ ⊗ a_n. -/
abbrev extraDegeneracy (n : ℕ) : chainLevel k A A n ⟶ chainLevel k A A (n + 1) :=
  extraDegeneracyWith k A 1 n

/-- Let k be commutative and A an associative unital ring with
k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}.
Inserting 1 at the front contracts the b′ complex:
b′ s + s b′ = id, including b′_1 s_0 = id in degree zero. -/
def bPrimeContraction : Homotopy (𝟙 (bPrimeComplex k A)) 0 :=
  bPrimeContractionOfLeftUnit k A 1 (fun a => one_mul a)

/-- Let k be commutative and A an associative unital ring with
k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}.
The degree-(n,n+1) component of the unit contraction of the b′
complex is the front-unit insertion s_n. -/
@[simp]
theorem bPrimeContraction_hom (n : ℕ) :
    (bPrimeContraction k A).hom n (n + 1) = extraDegeneracy k A n :=
  bPrimeContractionOfLeftUnit_hom k A 1 (fun a => one_mul a) n

/-- Let k be commutative and A an associative unital ring with a
k-module structure. Put C_n = A ⊗[k] A^{⊗n}.
The Connes boundary is B_n = (1 − t_{n+1}) s_n N_n,
where t_n is signed rotation and s_n inserts 1 at the front. -/
def connesBoundary (n : ℕ) : chainLevel k A A n ⟶ chainLevel k A A (n + 1) :=
  connesBoundaryWith k A 1 n

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Let k be commutative and A an associative unital ring with a
k-module structure. Put C_n = A ⊗[k] A^{⊗n}.
The Connes map C_n → C_{n+1} is the composite which first
applies N_n, then front-unit insertion s_n, then 1 − t_{n+1}. -/
theorem connesBoundary_eq (n : ℕ) :
    connesBoundary k A n = normMap k A n ≫ extraDegeneracy k A n ≫
      (𝟙 (chainLevel k A A (n + 1)) - cyclicMap k A (n + 1)) := rfl

/-- Let k be commutative and A an associative unital ring with
k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}.
The Connes boundary components define a homotopy from the zero
Hochschild chain map to itself. Its homotopy equation is bB + Bb = 0. -/
def connesBoundaryHomotopy : Homotopy (0 : bComplex k A ⟶ bComplex k A) 0 :=
  connesBoundaryHomotopyOfLeftUnit k A 1 (fun a => one_mul a)

/-- Let k be commutative and A an associative unital ring with
k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}.
The degree-(n,n+1) component of the zero-to-zero Connes homotopy
is the boundary B_n = (1 − t_{n+1}) s_n N_n. -/
@[simp]
theorem connesBoundaryHomotopy_hom (n : ℕ) :
    (connesBoundaryHomotopy k A).hom n (n + 1) = connesBoundary k A n :=
  connesBoundaryHomotopyOfLeftUnit_hom k A 1 (fun a => one_mul a) n

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Let k be commutative and A an associative unital ring with a
k-module structure. Put C_n = A ⊗[k] A^{⊗n}.
The consecutive Connes boundaries satisfy B_{n+1} B_n = 0
for every n ≥ 0. -/
theorem connesBoundary_square (n : ℕ) :
    connesBoundary k A n ≫ connesBoundary k A (n + 1) = 0 :=
  connesBoundaryWith_square k A 1 n

/-- Let k be commutative and A an associative unital ring with
k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}.
The Connes boundary anticommutes with the Hochschild boundary:
b_{n+2} B_{n+1} + B_n b_{n+1} = 0 on C_{n+1}. -/
theorem connesBoundary_mixed (n : ℕ) :
    let d₀ : chainLevel k A A (n + 1) ⟶ chainLevel k A A n :=
      (bComplex k A).d (n + 1) n
    let d₁ : chainLevel k A A (n + 2) ⟶ chainLevel k A A (n + 1) :=
      (bComplex k A).d (n + 2) (n + 1)
    connesBoundary k A (n + 1) ≫ d₁ + d₀ ≫ connesBoundary k A n = 0 :=
  connesBoundaryWith_mixed k A 1 (fun a => one_mul a) n

/-- Let k be commutative and A an associative unital ring with
k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}.
In degree zero the mixed relation is b_1 B_0 = 0. -/
theorem connesBoundary_comp_d_zero :
    connesBoundary k A 0 ≫ (bComplex k A).d 1 0 = 0 :=
  connesBoundaryWith_comp_d_zero k A 1 (fun a => one_mul a)

section Naturality

variable {k A} {B : Type w} [Ring B] [Module k B]

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Let k be commutative and A,B unital associative rings with k-module
structures. Let f : A → B be multiplicative and k-linear, with
the unit condition f(1_A) = 1_B. Applying f to every
tensor factor gives F_n, and the Connes operators satisfy
F_{n+1} B_n^A = B_n^B F_n across the independent carrier worlds. -/
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
/-- Let k be commutative and A an associative unital ring with a
k-module structure. Put C_n = A ⊗[k] A^{⊗n}.
The degree-zero Connes boundary has value
B_0(a) = 1 ⊗ a + a ⊗ 1. -/
theorem connesBoundary_zero_tprod (a : A) :
    (connesBoundary k A 0).hom
        (a ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin 0 => Fin.elim0 i)) =
      1 ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => a) +
        a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => (1 : A)) :=
  connesBoundaryWith_zero_tprod k A 1 a

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Let k be commutative and A an associative unital ring with a
k-module structure. Put C_n = A ⊗[k] A^{⊗n}.
The degree-one Connes boundary has value
B_1(a ⊗ b) = 1 ⊗ a ⊗ b − 1 ⊗ b ⊗ a
+ a ⊗ 1 ⊗ b − b ⊗ 1 ⊗ a. -/
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
