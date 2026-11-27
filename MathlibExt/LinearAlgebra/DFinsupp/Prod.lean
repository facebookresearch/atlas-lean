/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.LinearAlgebra.DFinsupp

/-!
# Dependent direct sums with product fibers

Let R be a semiring, I an arbitrary index type and M_i,N_i R-semimodules. Write ⊕iM_i for
dependent finitely supported vectors. The equivalence Φ:⊕i(M_i×N_i)≃ₗ[R](⊕iM_i)×(⊕iN_i) splits
coordinates, with inverse (m,n)↦(i↦(m_i,n_i)). The forward map takes coordinate projections;
the inverse support lies in the union of the two input supports.
-/

@[expose] public section

set_option autoImplicit false

universe uR uι uM uN

namespace DFinsupp

variable {R : Type uR} [Semiring R]
variable {ι : Type uι}
variable {M : ι → Type uM} {N : ι → Type uN}
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

/-- **Linear equivalence splitting product fibers.**

Let R be a semiring, I an arbitrary index type and M_i,N_i R-semimodules. Write ⊕iM_i for
dependent finitely supported vectors. The equivalence Φ:⊕i(M_i×N_i)≃ₗ[R](⊕iM_i)×(⊕iN_i) splits
coordinates, with inverse (m,n)↦(i↦(m_i,n_i)). The map prodLEquiv is Φ.
-/
def prodLEquiv :
    (Π₀ i, M i × N i) ≃ₗ[R] (Π₀ i, M i) × (Π₀ i, N i) where
  toFun x :=
    (DFinsupp.mapRange (fun _ p => p.1) (fun _ => rfl) x,
      DFinsupp.mapRange (fun _ p => p.2) (fun _ => rfl) x)
  invFun x :=
    DFinsupp.zipWith (fun _ m n => (m, n)) (fun _ => rfl) x.1 x.2
  left_inv x := by
    ext i <;> rfl
  right_inv x := by
    apply Prod.ext <;> ext i <;> rfl
  map_add' x y := by
    apply Prod.ext <;> ext i <;> rfl
  map_smul' r x := by
    apply Prod.ext <;> ext i <;> rfl

/-- **First projected direct-sum coordinate.**

Let R be a semiring, I an arbitrary index type and M_i,N_i R-semimodules. Write ⊕iM_i for
dependent finitely supported vectors. The equivalence Φ:⊕i(M_i×N_i)≃ₗ[R](⊕iM_i)×(⊕iN_i) splits
coordinates, with inverse (m,n)↦(i↦(m_i,n_i)). For x∈⊕i(M_i×N_i), Φ(x)_1(i)=x_i.1.
-/
@[simp]
theorem prodLEquiv_apply_fst_apply
    (x : Π₀ i, M i × N i) (i : ι) :
    (prodLEquiv (R := R) x).1 i = (x i).1 :=
  rfl

/-- **Second projected direct-sum coordinate.**

Let R be a semiring, I an arbitrary index type and M_i,N_i R-semimodules. Write ⊕iM_i for
dependent finitely supported vectors. The equivalence Φ:⊕i(M_i×N_i)≃ₗ[R](⊕iM_i)×(⊕iN_i) splits
coordinates, with inverse (m,n)↦(i↦(m_i,n_i)). For x∈⊕i(M_i×N_i), Φ(x)_2(i)=x_i.2.
-/
@[simp]
theorem prodLEquiv_apply_snd_apply
    (x : Π₀ i, M i × N i) (i : ι) :
    (prodLEquiv (R := R) x).2 i = (x i).2 :=
  rfl

/-- **Coordinate of the inverse product assembly.**

Let R be a semiring, I an arbitrary index type and M_i,N_i R-semimodules. Write ⊕iM_i for
dependent finitely supported vectors. The equivalence Φ:⊕i(M_i×N_i)≃ₗ[R](⊕iM_i)×(⊕iN_i) splits
coordinates, with inverse (m,n)↦(i↦(m_i,n_i)). For m∈⊕iM_i,n∈⊕iN_i, Φ⁻¹(m,n)_i=(m_i,n_i).
-/
@[simp]
theorem prodLEquiv_symm_apply_apply
    (x : (Π₀ i, M i) × (Π₀ i, N i)) (i : ι) :
    ((prodLEquiv (R := R)).symm x) i = (x.1 i, x.2 i) :=
  rfl

/-- **Splitting a single product-fiber vector.**

Let R be a semiring, I an arbitrary index type and M_i,N_i R-semimodules. Write ⊕iM_i for
dependent finitely supported vectors. The equivalence Φ:⊕i(M_i×N_i)≃ₗ[R](⊕iM_i)×(⊕iN_i) splits
coordinates, with inverse (m,n)↦(i↦(m_i,n_i)). For i∈I and (m,n)∈M_i×N_i, Φ(δ_i(m,n))=(δ_i
m,δ_i n), where δ_i is the one-coordinate vector.
-/
@[simp]
theorem prodLEquiv_single [DecidableEq ι]
    (i : ι) (x : M i × N i) :
    prodLEquiv (R := R) (DFinsupp.single i x) =
      (DFinsupp.single i x.1, DFinsupp.single i x.2) := by
  apply Prod.ext
  · exact DFinsupp.mapRange_single
      (f := fun i (p : M i × N i) => p.1) (hf := fun _ => rfl)
  · exact DFinsupp.mapRange_single
      (f := fun i (p : M i × N i) => p.2) (hf := fun _ => rfl)

/-- **Combining two single vectors at the same index.**

Let R be a semiring, I an arbitrary index type and M_i,N_i R-semimodules. Write ⊕iM_i for
dependent finitely supported vectors. The equivalence Φ:⊕i(M_i×N_i)≃ₗ[R](⊕iM_i)×(⊕iN_i) splits
coordinates, with inverse (m,n)↦(i↦(m_i,n_i)). For i∈I,m∈M_i,n∈N_i, Φ⁻¹(δ_i m,δ_i n)=δ_i(m,n).
-/
@[simp]
theorem prodLEquiv_symm_single_single [DecidableEq ι]
    (i : ι) (m : M i) (n : N i) :
    (prodLEquiv (R := R)).symm
        (DFinsupp.single i m, DFinsupp.single i n) =
      DFinsupp.single i (m, n) := by
  exact DFinsupp.zipWith_single_single
    (fun _ m n => (m, n)) (fun _ => rfl) m n

end DFinsupp

end
