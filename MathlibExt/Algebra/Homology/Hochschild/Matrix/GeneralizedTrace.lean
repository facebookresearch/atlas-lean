/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Generalized trace on coefficient tensor words

Let k be a commutative ring, A,M k-modules and ι a finite index type.
The k-linear generalized trace
Tr_n:Mat_ι(M)⊗[k]Mat_ι(A)^{⊗n}→M⊗[k]A^{⊗n}
sums over closed index cycles:
Tr_n(X⊗B_1⊗⋯⊗B_n)=
∑_{i_0,…,i_n} X_{i_0,i_1}⊗(B_1)_{i_1,i_2}⊗⋯⊗(B_n)_{i_n,i_0}.
Successor indices are modulo n+1, so degree zero is additive diagonal trace.

The single-corner inclusion at b∈ι is a section of Tr_n.
Entrywise k-linear maps of coefficient and algebra modules preserve
the formula. For ground scalar matrices U_0,…,U_n, the trace of
their coefficient-scaled word is tr(U_0⋯U_n) times the underlying tensor.

Reference: J.-L. Loday, Cyclic Homology, §§1.2.0–1.2.2.
-/

@[expose] public section

noncomputable section

open scoped BigOperators TensorProduct

namespace ModuleCat.Algebra.Hochschild.Matrix

universe u v w z v' w'

variable (k : Type u) [CommRing k] (ι : Type z)
variable {A : Type v} [AddCommGroup A] [Module k A]
variable {M : Type w} [AddCommGroup M] [Module k M]

variable [Fintype ι]

/-- For k commutative, M a k-module and finite ι with decidable equality, the k-linear
equivalence Mat_ι(k)⊗[k]M≃Mat_ι(M) sends U⊗m to the
entrywise scalar matrix (U_{ij}•m). -/
def matrixTensorEquiv [DecidableEq ι] : Matrix ι ι k ⊗[k] M ≃ₗ[k] Matrix ι ι M := by
  exact (TensorProduct.comm k (Matrix ι ι k) M).trans
    ((TensorProduct.congr (LinearEquiv.refl k M) (Matrix.ofLinearEquiv k).symm).trans
      ((TensorProduct.piRight k k M (fun _ : ι => ι → k)).trans
        ((LinearEquiv.piCongrRight fun _ : ι =>
          TensorProduct.piScalarRight k k M ι).trans (Matrix.ofLinearEquiv k))))

/-- For k commutative, M a k-module and finite ι with decidable equality, the finite
matrix tensor equivalence satisfies (U⊗m)_{ij}↦U_{ij}•m. -/
@[simp]
theorem matrixTensorEquiv_tmul [DecidableEq ι] (U : Matrix ι ι k) (m : M) (i j : ι) :
    matrixTensorEquiv k ι (U ⊗ₜ[k] m) i j = U i j • m := by
  classical
  change TensorProduct.piScalarRight k k M ι
      ((TensorProduct.piRight k k M (fun _ : ι => ι → k))
        (m ⊗ₜ[k] (Matrix.ofLinearEquiv k).symm U) i) j = U i j • m
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  rfl

/-- Let k be a commutative ring, A and M k-modules, and ι a finite
index type. Set C_n(A,M)=M⊗[k]A^{⊗n}.
The generalized trace is the k-linear sum over closed cycles of
n+1 indices, with the coefficient entry first and the last algebra
entry returning to the first vertex. -/
def generalizedTrace (n : ℕ) :
    Matrix ι ι M ⊗[k] TensorPower k n (Matrix ι ι A) →ₗ[k]
      M ⊗[k] TensorPower k n A := by
  classical
  exact ∑ γ : Fin (n + 1) → ι,
    TensorProduct.map (Matrix.entryLinearMap k M (γ 0) (γ 1))
      (PiTensorProduct.map fun j : Fin n =>
        Matrix.entryLinearMap k A (γ j.succ) (γ (j.succ + 1)))

/-- Let k be a commutative ring, A and M k-modules, and ι a finite
index type. Set C_n(A,M)=M⊗[k]A^{⊗n}.
For X∈Mat_ι(M) and B_j∈Mat_ι(A), the trace is
∑_{i_0,…,i_n}X_{i_0,i_1}⊗(B_1)_{i_1,i_2}⊗⋯⊗(B_n)_{i_n,i_0},
with successor indices modulo n+1. -/
theorem generalizedTrace_tmul_tprod (n : ℕ) (m : Matrix ι ι M)
    (a : Fin n → Matrix ι ι A) :
    generalizedTrace k ι n (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ∑ γ : Fin (n + 1) → ι, m (γ 0) (γ 1) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j => a j (γ j.succ) (γ (j.succ + 1))) := by
  classical
  simp only [generalizedTrace, LinearMap.sum_apply, TensorProduct.map_tmul,
    PiTensorProduct.map_tprod, Matrix.entryLinearMap_apply]

section Corner

variable [DecidableEq ι]

/-- Let k be commutative, A,M k-modules, ι have decidable equality and b∈ι.
The corner tensor map applies the single-entry (b,b) inclusion to
the coefficient and to all n tail factors. -/
def cornerTensor (b : ι) (n : ℕ) :
    M ⊗[k] TensorPower k n A →ₗ[k]
      Matrix ι ι M ⊗[k] TensorPower k n (Matrix ι ι A) :=
  TensorProduct.map (Matrix.singleLinearMap k b b)
    (PiTensorProduct.map fun _ : Fin n => Matrix.singleLinearMap k b b)

omit [Fintype ι] in
@[simp]
theorem cornerTensor_tmul_tprod (b : ι) (n : ℕ) (m : M) (a : Fin n → A) :
    cornerTensor k ι b n (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      Matrix.singleLinearMap k b b m ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j => Matrix.singleLinearMap k b b (a j)) := by
  simp only [cornerTensor, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
omit [Fintype ι] in
/-- Let k be commutative, A,M k-modules, ι have decidable equality, and b be an index. In a
corner-inserted tensor, each cycle other than the constant cycle at b has a
zero entry, so its generalized-trace summand is zero. -/
private theorem corner_summand_eq_zero (b : ι) (n : ℕ) (m : M) (a : Fin n → A)
    (γ : Fin (n + 1) → ι) (hγ : γ ≠ fun _ => b) :
    Matrix.singleLinearMap k b b m (γ 0) (γ 1) ⊗ₜ[k]
      PiTensorProduct.tprod k
        (fun j => Matrix.singleLinearMap k b b (a j) (γ j.succ) (γ (j.succ + 1))) = 0 := by
  classical
  have hn : ¬ ∀ j, γ j = b := fun h => hγ (funext h)
  obtain ⟨j, hj⟩ := not_forall.mp hn
  revert hj
  refine Fin.cases ?_ (fun j => ?_) j
  · intro hj
    simp only [Matrix.singleLinearMap_apply, Matrix.single_apply, eq_comm, ite_and, hj, ite_false,
      TensorProduct.zero_tmul]
  · intro hj
    have hz :
        (fun i : Fin n => Matrix.singleLinearMap k b b (a i)
          (γ i.succ) (γ (i.succ + 1))) j = 0 := by
      simp only [Matrix.singleLinearMap_apply, Matrix.single_apply, eq_comm, ite_and, hj, ite_false]
    rw [(PiTensorProduct.tprod k).map_coord_zero j hz, TensorProduct.tmul_zero]

/-- Let k be a commutative ring, A and M k-modules, and ι a finite
index type. Set C_n(A,M)=M⊗[k]A^{⊗n}.
For b∈ι, generalized trace of the corner-inserted tensor
E_{bb}(m)⊗E_{bb}(a_1)⊗⋯⊗E_{bb}(a_n) is m⊗a_1⊗⋯⊗a_n. -/
theorem generalizedTrace_corner_tprod (b : ι) (n : ℕ) (m : M) (a : Fin n → A) :
    generalizedTrace k ι n
      (Matrix.singleLinearMap k b b m ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j => Matrix.singleLinearMap k b b (a j))) =
      m ⊗ₜ[k] PiTensorProduct.tprod k a := by
  classical
  rw [generalizedTrace_tmul_tprod]
  calc
    _ = Matrix.singleLinearMap k b b m b b ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j => Matrix.singleLinearMap k b b (a j) b b) := by
      apply Finset.sum_eq_single (fun _ : Fin (n + 1) => b)
      · intro γ _ hγ
        exact corner_summand_eq_zero k ι b n m a γ hγ
      · simp
    _ = m ⊗ₜ[k] PiTensorProduct.tprod k a := by
      simp only [Matrix.singleLinearMap_apply, Matrix.single_apply, eq_comm, ite_and, ite_true]

/-- Let k be a commutative ring, A and M k-modules, and ι a finite
index type. Set C_n(A,M)=M⊗[k]A^{⊗n}.
For b∈ι, the full k-linear composite of corner tensor inclusion
followed by generalized trace is id_{C_n(A,M)}. -/
theorem generalizedTrace_comp_cornerTensor (b : ι) (n : ℕ) :
    (generalizedTrace k ι n).comp (cornerTensor k ι b n) =
      (LinearMap.id : M ⊗[k] TensorPower k n A →ₗ[k] M ⊗[k] TensorPower k n A) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro a
  change generalizedTrace k ι n
    (cornerTensor k ι b n (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      m ⊗ₜ[k] PiTensorProduct.tprod k a
  rw [cornerTensor_tmul_tprod]
  exact generalizedTrace_corner_tprod k ι b n m a

end Corner

/-- Let k be a commutative ring, A and M k-modules, and ι a finite
index type. Set C_n(A,M)=M⊗[k]A^{⊗n}.
In degree zero, Tr_0(X⊗empty)=tr(X)⊗empty,
where tr(X)=∑_{i∈ι}X_{ii} is the additive matrix trace. -/
theorem generalizedTrace_zero (m : Matrix ι ι M) :
    generalizedTrace k ι 0
      (m ⊗ₜ[k] PiTensorProduct.tprod k
        (fun j : Fin 0 => (j.elim0 : Matrix ι ι A))) =
      Matrix.trace m ⊗ₜ[k] PiTensorProduct.tprod k (fun j : Fin 0 => (j.elim0 : A)) := by
  classical
  rw [generalizedTrace_tmul_tprod]
  have hw (γ : Fin 1 → ι) :
      (fun j : Fin 0 => (fun i : Fin 0 => (i.elim0 : Matrix ι ι A)) j
        (γ j.succ) (γ (j.succ + 1))) = (fun j : Fin 0 => (j.elim0 : A)) := by
    funext j
    exact j.elim0
  simp_rw [hw]
  calc
    _ = ∑ i : ι, m i i ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j : Fin 0 => (j.elim0 : A)) :=
      Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _ _ (fun _ => rfl)
    _ = (∑ i : ι, m i i) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j : Fin 0 => (j.elim0 : A)) :=
      (TensorProduct.sum_tmul Finset.univ _ _).symm
    _ = _ := rfl

/-- Let k be a commutative ring, A and M k-modules, and ι a finite
index type. Set C_n(A,M)=M⊗[k]A^{⊗n}.
If ι is empty, the generalized trace is zero in every degree. -/
theorem generalizedTrace_of_isEmpty [IsEmpty ι] (n : ℕ) :
    (generalizedTrace k ι n : Matrix ι ι M ⊗[k] TensorPower k n (Matrix ι ι A) →ₗ[k]
      M ⊗[k] TensorPower k n A) = 0 := by
  classical
  let : IsEmpty (Fin (n + 1) → ι) := ⟨fun γ => isEmptyElim (γ 0)⟩
  simp only [generalizedTrace, Finset.univ_eq_empty, Finset.sum_empty]

section Naturality

variable {B : Type v'} [AddCommGroup B] [Module k B]
variable {N : Type w'} [AddCommGroup N] [Module k N]

/-- Let k be commutative, A,M,B,N k-modules in independent
carrier universes and ι finite. For k-linear f:M→N and g:A→B,
(f⊗g^{⊗n})Tr_{M,A}=Tr_{N,B}(f^{Mat}⊗(g^{Mat})^{⊗n}). -/
theorem generalizedTrace_naturality (n : ℕ) (f : M →ₗ[k] N) (g : A →ₗ[k] B) :
    (TensorProduct.map f (PiTensorProduct.map fun _ : Fin n => g)).comp
        (generalizedTrace k ι n) =
      (generalizedTrace k ι n).comp
        (TensorProduct.map f.mapMatrix
          (PiTensorProduct.map fun _ : Fin n => g.mapMatrix)) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro a
  change TensorProduct.map f (PiTensorProduct.map fun _ : Fin n => g)
      (generalizedTrace k ι n (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    generalizedTrace k ι n
      (TensorProduct.map f.mapMatrix
        (PiTensorProduct.map fun _ : Fin n => g.mapMatrix)
        (m ⊗ₜ[k] PiTensorProduct.tprod k a))
  simp only [TensorProduct.map_tmul, PiTensorProduct.map_tprod,
    generalizedTrace_tmul_tprod, map_sum, LinearMap.mapMatrix_apply, Matrix.map_apply]

end Naturality

/-- For k commutative, finite ι and ground matrices U_0,…,U_n,
the closed-cycle weight is
∑_{i_0,…,i_n}(U_0)_{i_0,i_1}(U_1)_{i_1,i_2}⋯(U_n)_{i_n,i_0},
with cyclic successor indices. -/
def traceWeight (n : ℕ) (U₀ : Matrix ι ι k) (U : Fin n → Matrix ι ι k) : k := by
  classical
  exact ∑ γ : Fin (n + 1) → ι,
    U₀ (γ 0) (γ 1) * ∏ j : Fin n, U j (γ j.succ) (γ (j.succ + 1))

/-- Let k be a commutative ring, A and M k-modules, and ι a finite
index type. Set C_n(A,M)=M⊗[k]A^{⊗n}.
For U_0,…,U_n∈Mat_ι(k), scaling m and the tail a_j
entrywise gives trace equal to the closed-cycle weight times
m⊗a_1⊗⋯⊗a_n. -/
theorem generalizedTrace_scaled_weight (n : ℕ) (U₀ : Matrix ι ι k)
    (U : Fin n → Matrix ι ι k) (m : M) (a : Fin n → A) :
    generalizedTrace k ι n
      ((U₀.map (fun c => c • m)) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun t => (U t).map (fun c => c • a t))) =
      traceWeight k ι n U₀ U • (m ⊗ₜ[k] PiTensorProduct.tprod k a) := by
  classical
  rw [generalizedTrace_tmul_tprod]
  simp only [Matrix.map_apply]
  have hw (γ : Fin (n + 1) → ι) :
      PiTensorProduct.tprod k
        (fun j => U j (γ j.succ) (γ (j.succ + 1)) • a j) =
      (∏ j : Fin n, U j (γ j.succ) (γ (j.succ + 1))) •
        PiTensorProduct.tprod k a :=
    (PiTensorProduct.tprod k).map_smul_univ _ _
  simp_rw [hw, TensorProduct.smul_tmul_smul]
  rw [← Finset.sum_smul]
  rfl

/-- For k commutative and finite ι with decidable equality,
(W_0⋯W_n)_{st}=∑_{i_1,…,i_n}(W_0)_{s,i_1}⋯(W_n)_{i_n,t}.
The empty internal path for n=0 gives (W_0)_{st}. -/
theorem matrix_word_entry [DecidableEq ι] :
    ∀ (n : ℕ) (W : Fin (n + 1) → Matrix ι ι k) (s t : ι),
      (List.ofFn W).prod s t =
        ∑ γ : Fin n → ι, ∏ j : Fin (n + 1),
          W j ((Fin.cons (α := fun _ => ι) s
            (Fin.snoc (α := fun _ => ι) γ t)) j.castSucc)
            ((Fin.cons (α := fun _ => ι) s
              (Fin.snoc (α := fun _ => ι) γ t)) j.succ) := by
  intro n
  induction n with
  | zero =>
      intro W s t
      let : Unique (Fin 0 → ι) :=
        { default := fun j => j.elim0
          uniq := fun γ => funext fun j => j.elim0 }
      simp [List.ofFn_succ, Fin.snoc_zero]
  | succ n ih =>
      intro W s t
      let T : Fin (n + 1) → Matrix ι ι k := fun j => W j.succ
      calc
        (List.ofFn W).prod s t =
            ∑ a : ι, W 0 s a * (List.ofFn T).prod a t := by
          rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
        _ = ∑ a : ι, ∑ γ : Fin n → ι, W 0 s a *
            ∏ j : Fin (n + 1),
              T j ((Fin.cons (α := fun _ => ι) a
                (Fin.snoc (α := fun _ => ι) γ t)) j.castSucc)
                ((Fin.cons (α := fun _ => ι) a
                  (Fin.snoc (α := fun _ => ι) γ t)) j.succ) := by
          simp_rw [ih, Finset.mul_sum]
        _ = ∑ p : ι × (Fin n → ι), W 0 s p.1 *
            ∏ j : Fin (n + 1),
              T j ((Fin.cons (α := fun _ => ι) p.1
                (Fin.snoc (α := fun _ => ι) p.2 t)) j.castSucc)
                ((Fin.cons (α := fun _ => ι) p.1
                  (Fin.snoc (α := fun _ => ι) p.2 t)) j.succ) := by
          rw [Fintype.sum_prod_type]
        _ = ∑ γ : Fin (n + 1) → ι, ∏ j : Fin (n + 2),
            W j ((Fin.cons (α := fun _ => ι) s
              (Fin.snoc (α := fun _ => ι) γ t)) j.castSucc)
              ((Fin.cons (α := fun _ => ι) s
                (Fin.snoc (α := fun _ => ι) γ t)) j.succ) := by
          apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => ι))
          intro p
          rcases p with ⟨a, γ⟩
          change W 0 s a *
              (∏ j : Fin (n + 1),
                T j ((Fin.cons (α := fun _ => ι) a
                  (Fin.snoc (α := fun _ => ι) γ t)) j.castSucc)
                  ((Fin.cons (α := fun _ => ι) a
                    (Fin.snoc (α := fun _ => ι) γ t)) j.succ)) =
            ∏ j : Fin (n + 2),
              W j ((Fin.cons (α := fun _ => ι) s
                (Fin.snoc (α := fun _ => ι) (Fin.cons (α := fun _ => ι) a γ) t)) j.castSucc)
                ((Fin.cons (α := fun _ => ι) s
                  (Fin.snoc (α := fun _ => ι) (Fin.cons (α := fun _ => ι) a γ) t)) j.succ)
          have hv : Fin.cons (α := fun _ => ι) s
              (Fin.snoc (α := fun _ => ι) (Fin.cons (α := fun _ => ι) a γ) t) =
              Fin.cons (α := fun _ => ι) s
                (Fin.cons (α := fun _ => ι) a (Fin.snoc (α := fun _ => ι) γ t)) :=
            congrArg (Fin.cons (α := fun _ => ι) s)
              (Fin.cons_snoc_eq_snoc_cons a γ t).symm
          rw [hv]
          conv_rhs => rw [Fin.prod_univ_succ]
          simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
            ← Fin.succ_castSucc, T]
omit [Fintype ι] in
/-- For γ:Fin(n+1)→ι, append γ_0 to close the vertex family.
Its successor entry at j is γ_{j+1 mod(n+1)}. -/
private theorem closed_snoc_succ {n : ℕ} (γ : Fin (n + 1) → ι)
    (j : Fin (n + 1)) :
    Fin.snoc (α := fun _ => ι) γ (γ 0) j.succ = γ (j + 1) := by
  rw [← finRotate_apply]
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.succ_last, Fin.snoc_last, finRotate_last]
  · rw [Fin.succ_castSucc, Fin.snoc_castSucc]
    exact congrArg γ (finRotate_of_lt i.isLt).symm

/-- For k commutative and finite ι with decidable equality,
the closed-cycle weight of U_0,…,U_n is tr(U_0(U_1⋯U_n)),
with the matrix word kept in its given order. -/
theorem traceWeight_eq_trace_product [DecidableEq ι] (n : ℕ)
    (U₀ : Matrix ι ι k) (U : Fin n → Matrix ι ι k) :
    traceWeight k ι n U₀ U = Matrix.trace (U₀ * (List.ofFn U).prod) := by
  classical
  let W : Fin (n + 1) → Matrix ι ι k :=
    Fin.cons (α := fun _ => Matrix ι ι k) U₀ U
  calc
    traceWeight k ι n U₀ U =
        ∑ δ : Fin (n + 1) → ι, ∏ j : Fin (n + 1), W j (δ j) (δ (j + 1)) := by
      unfold traceWeight
      apply Finset.sum_congr rfl
      intro δ _
      rw [Fin.prod_univ_succ]
      simp only [W, Fin.cons_zero, Fin.cons_succ, zero_add]
    _ = ∑ p : ι × (Fin n → ι), ∏ j : Fin (n + 1),
        W j ((Fin.cons (α := fun _ => ι) p.1 p.2) j)
          ((Fin.cons (α := fun _ => ι) p.1 p.2) (j + 1)) :=
      (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => ι)) _ _
        (fun _ => rfl)).symm
    _ = ∑ s : ι, ∑ γ : Fin n → ι, ∏ j : Fin (n + 1),
        W j ((Fin.cons (α := fun _ => ι) s γ) j)
          ((Fin.cons (α := fun _ => ι) s γ) (j + 1)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ s : ι, ∑ γ : Fin n → ι, ∏ j : Fin (n + 1),
        W j ((Fin.cons (α := fun _ => ι) s
          (Fin.snoc (α := fun _ => ι) γ s)) j.castSucc)
          ((Fin.cons (α := fun _ => ι) s
            (Fin.snoc (α := fun _ => ι) γ s)) j.succ) := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro γ _
      rw [Fin.cons_snoc_eq_snoc_cons]
      apply Finset.prod_congr rfl
      intro j _
      rw [Fin.snoc_castSucc]
      have hlast :
          Fin.snoc (α := fun _ => ι) (Fin.cons (α := fun _ => ι) s γ) s j.succ =
            (Fin.cons (α := fun _ => ι) s γ) (j + 1) := by
        simpa only [Fin.cons_zero] using
          closed_snoc_succ ι (Fin.cons (α := fun _ => ι) s γ) j
      exact congrArg
        (fun t : ι => Matrix.entryLinearMap k k
          ((Fin.cons (α := fun _ => ι) s γ) j) t (W j)) hlast.symm
    _ = ∑ s : ι, (List.ofFn W).prod s s := by
      apply Finset.sum_congr rfl
      intro s _
      exact (matrix_word_entry k ι n W s s).symm
    _ = Matrix.trace (U₀ * (List.ofFn U).prod) := by
      simp only [W, List.ofFn_cons, List.prod_cons, Matrix.trace, Matrix.diag_apply]

/-- Let k be a commutative ring, A and M k-modules, and ι a finite
index type. Set C_n(A,M)=M⊗[k]A^{⊗n}.
For ι with decidable equality, entrywise ground-matrix scaling gives
Tr_n((U_0•m)⊗(U_1•a_1)⊗⋯⊗(U_n•a_n))
=tr(U_0⋯U_n)•(m⊗a_1⊗⋯⊗a_n). -/
theorem generalizedTrace_scaled [DecidableEq ι] (n : ℕ) (U₀ : Matrix ι ι k)
    (U : Fin n → Matrix ι ι k) (m : M) (a : Fin n → A) :
    generalizedTrace k ι n
      ((U₀.map (fun c => c • m)) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun t => (U t).map (fun c => c • a t))) =
      Matrix.trace (U₀ * (List.ofFn U).prod) • (m ⊗ₜ[k] PiTensorProduct.tprod k a) := by
  rw [generalizedTrace_scaled_weight, traceWeight_eq_trace_product]

end ModuleCat.Algebra.Hochschild.Matrix
