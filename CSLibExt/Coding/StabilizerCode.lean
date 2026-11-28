/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.QuantumCodeDistance
public import MathlibExt.Quantum.PauliXZ
import Mathlib.LinearAlgebra.Trace


/-!
# Dimension of a stabilizer code

The dimension of a stabilizer code: `r` independent commuting signed Pauli generators on `n` qubits cut out a `2 ^ (n - r)`-dimensional code space (Gottesman, Sec. 3.2).
-/

@[expose] public section

open scoped Matrix
open Cslib.CodingTheory.CSS
namespace Cslib.CodingTheory.StabilizerCode

set_option autoImplicit false

/-- The `j`-th signed Pauli generator. -/
noncomputable def generator {n r : ℕ} (a b : Fin r → Fin n → ZMod 2) (c : Fin r → ℂ) (j : Fin r) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  c j • pauli (a j) (b j)

/-- The product of the generators indexed by `T`, in index order. -/
noncomputable def groupElem {n r : ℕ} (a b : Fin r → Fin n → ZMod 2) (c : Fin r → ℂ)
    (T : Finset (Fin r)) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  (List.ofFn fun j => if j ∈ T then generator a b c j else 1).prod

/-- The stabilizer group as a finset of subset products. -/
noncomputable def stabilizerGroup {n r : ℕ} (a b : Fin r → Fin n → ZMod 2) (c : Fin r → ℂ) :
    Finset (Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) := by
  classical
  exact Finset.univ.image (groupElem a b c)

/-- The common `+1` eigenspace of the generators. -/
noncomputable def codeSpace {n r : ℕ} (a b : Fin r → Fin n → ZMod 2) (c : Fin r → ℂ) :
    Submodule ℂ ((Fin n → ZMod 2) → ℂ) :=
  ⨅ j, LinearMap.ker (Matrix.toLin' (generator a b c j) - LinearMap.id)

/-- The group-average projector onto the code space. -/
noncomputable def codeProjector {n r : ℕ} (a b : Fin r → Fin n → ZMod 2) (c : Fin r → ℂ) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  ((stabilizerGroup a b c).card : ℂ)⁻¹ • ∑ s ∈ stabilizerGroup a b c, s

/-- Pointwise products of `ofFn` lists multiply. -/
private theorem ofFn_prod_mul {M : Type*} [Monoid M] {r : ℕ} (f g h : Fin r → M)
    (hp : ∀ j, f j * g j = h j) (hc : ∀ i j, Commute (f i) (g j)) :
    (List.ofFn f).prod * (List.ofFn g).prod = (List.ofFn h).prod := by
  induction r with
  | zero =>
    rw [List.ofFn_zero, List.ofFn_zero, List.ofFn_zero, List.prod_nil, mul_one]
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    have hmid : Commute (List.ofFn fun i : Fin n => f i.succ).prod (g 0) :=
      Commute.list_prod_left _ _ ((List.forall_mem_ofFn_iff).mpr (fun i => hc i.succ 0))
    have hIH : (List.ofFn fun i : Fin n => f i.succ).prod *
          (List.ofFn fun i : Fin n => g i.succ).prod =
          (List.ofFn fun i : Fin n => h i.succ).prod :=
      ih _ _ _ (fun i => hp i.succ) (fun i j => hc i.succ j.succ)
    rw [Commute.mul_mul_mul_comm hmid _ _, hp 0, hIH]

/-- Subset products multiply by symmetric difference. -/
theorem groupElem_mul {n r : ℕ} {a b : Fin r → Fin n → ZMod 2} {c : Fin r → ℂ}
    (hsq : ∀ j, generator a b c j * generator a b c j = 1)
    (hcomm : ∀ j k, Commute (generator a b c j) (generator a b c k)) (T T' : Finset (Fin r)) :
    groupElem a b c T * groupElem a b c T' = groupElem a b c (symmDiff T T') := by
  refine ofFn_prod_mul _ _ _ ?_ ?_
  · intro j
    by_cases hjT : j ∈ T <;> by_cases hjT' : j ∈ T'
    · rw [ite_eq_left hjT, ite_eq_left hjT', hsq j]
      have hmem : j ∉ symmDiff T T' := by
        intro hcon
        rw [Finset.mem_symmDiff] at hcon
        rcases hcon with ⟨_, hn⟩ | ⟨_, hn⟩ <;> contradiction
      rw [ite_eq_right hmem]
    · rw [ite_eq_left hjT, ite_eq_right hjT', mul_one]
      have hmem : j ∈ symmDiff T T' := by
        rw [Finset.mem_symmDiff]
        exact Or.inl ⟨hjT, hjT'⟩
      rw [ite_eq_left hmem]
    · rw [ite_eq_right hjT, ite_eq_left hjT', one_mul]
      have hmem : j ∈ symmDiff T T' := by
        rw [Finset.mem_symmDiff]
        exact Or.inr ⟨hjT', hjT⟩
      rw [ite_eq_left hmem]
    · rw [ite_eq_right hjT, ite_eq_right hjT', mul_one]
      have hmem : j ∉ symmDiff T T' := by
        intro hcon
        rw [Finset.mem_symmDiff] at hcon
        rcases hcon with ⟨h, _⟩ | ⟨h, _⟩ <;> contradiction
      rw [ite_eq_right hmem]
  · intro i j
    by_cases hiT : i ∈ T <;> by_cases hjT' : j ∈ T' <;> simp only [hiT, hjT', ite_true, ite_false]
    · exact hcomm i j
    · exact Commute.one_right _
    · exact Commute.one_left _
    · exact Commute.one_right _

/-- The two `X^a Z^b` carriers agree (helper form). -/
private theorem pauli_eq_pauliXZ_aux {n : ℕ} (a b : Fin n → ZMod 2) :
    pauli a b = MathlibExt.Quantum.PauliXZ.pauliXZ a b :=
  rfl

/-- Product of Pauli operators, with the phase as a `sign`. -/
private theorem pauli_mul {n : ℕ} (a b a' b' : Fin n → ZMod 2) :
    pauli a b * pauli a' b' = sign (b ⬝ᵥ a') • pauli (a + a') (b + b') := by
  rw [pauli_eq_pauliXZ_aux, pauli_eq_pauliXZ_aux, pauli_eq_pauliXZ_aux,
    MathlibExt.Quantum.PauliXZ.pauliXZ_mul]
  rfl

/-- The identity Pauli operator is `1`. -/
private theorem pauli_zero_zero {n : ℕ} : pauli (0 : Fin n → ZMod 2) 0 = 1 := by
  ext u v
  simp only [pauli, Matrix.of_apply, add_zero, zero_dotProduct, sign_zero, Matrix.one_apply]

/-- A Pauli operator is Hermitian up to its square sign. -/
private theorem pauli_conjTranspose {n : ℕ} (a b : Fin n → ZMod 2) :
    (pauli a b)ᴴ = sign (b ⬝ᵥ a) • pauli a b := by
  have hiff : ∀ u v : Fin n → ZMod 2, (v = u + a) ↔ (u = v + a) := by
    intro u v
    constructor
    · rintro rfl; rw [add_assoc, add_self_eq_zero, add_zero]
    · rintro rfl; rw [add_assoc, add_self_eq_zero, add_zero]
  ext u v
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, pauli,
    Matrix.of_apply]
  by_cases huv : u = v + a
  · rw [ite_eq_left huv, ite_eq_left ((hiff u v).mpr huv), star_sign]
    subst huv
    rw [dotProduct_add, sign_add, mul_comm]
  · rw [ite_eq_right huv, ite_eq_right (fun h => huv ((hiff u v).mp h)), star_zero, mul_zero]

/-- The square of a Pauli operator is its sign times `1`. -/
private theorem pauli_sq {n : ℕ} (a b : Fin n → ZMod 2) :
    pauli a b * pauli a b = sign (b ⬝ᵥ a) • 1 := by
  rw [pauli_mul, add_self_eq_zero, add_self_eq_zero, pauli_zero_zero]

/-- A `sign` is never `0`. -/
private theorem sign_ne_zero (x : ZMod 2) : sign x ≠ 0 := by
  intro h
  have h1 := sign_mul_self x
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

/-- `sign` is injective. -/
private theorem sign_inj {x y : ZMod 2} (h : sign x = sign y) : x = y := by
  have h2 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  rcases h2 x with rfl | rfl <;> rcases h2 y with rfl | rfl
  · rfl
  · rw [sign_zero, sign_one] at h; exact absurd h (by norm_num)
  · rw [sign_one, sign_zero] at h; exact absurd h (by norm_num)
  · rfl

/-- A generator scalar is never `0`. -/
private theorem generator_scalar_ne_zero {n r : ℕ} {a b : Fin r → Fin n → ZMod 2}
    {c : Fin r → ℂ} (hsq : ∀ j, generator a b c j * generator a b c j = 1) (j : Fin r) :
    c j ≠ 0 := by
  intro hcz
  have h0 : generator a b c j = 0 := by simp [generator, hcz]
  have h1 := hsq j
  rw [h0, mul_zero] at h1
  have hentry := congrFun (congrFun h1 0) 0
  simp at hentry

/-- A generator squaring to `1` constrains its scalar. -/
private theorem generator_sq_scalar {n r : ℕ} {a b : Fin r → Fin n → ZMod 2}
    {c : Fin r → ℂ} (hsq : ∀ j, generator a b c j * generator a b c j = 1) (j : Fin r) :
    (c j) ^ 2 * sign ((b j) ⬝ᵥ (a j)) = 1 := by
  have h1 : (c j • pauli (a j) (b j)) * (c j • pauli (a j) (b j)) = 1 := hsq j
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauli_sq, smul_smul] at h1
  have hentry := congrFun (congrFun h1 0) 0
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq] at hentry
  rw [mul_one] at hentry
  rw [pow_two]
  exact hentry

/-- A generator scalar has modulus `1`. -/
private theorem generator_star_mul_self {n r : ℕ} {a b : Fin r → Fin n → ZMod 2}
    {c : Fin r → ℂ} (hsq : ∀ j, generator a b c j * generator a b c j = 1) (j : Fin r) :
    star (c j) * c j = 1 := by
  have hcsq := generator_sq_scalar hsq j
  have hσsq : sign ((b j) ⬝ᵥ (a j)) * sign ((b j) ⬝ᵥ (a j)) = 1 :=
    sign_mul_self _
  have hc2 : (c j) ^ 2 = sign ((b j) ⬝ᵥ (a j)) := by
    have hmul := congrArg (· * sign ((b j) ⬝ᵥ (a j))) hcsq
    rw [mul_assoc, hσsq, mul_one, one_mul] at hmul
    exact hmul
  have hx2 : (star (c j) * c j) ^ 2 = 1 := by
    have hring : (star (c j) * c j) ^ 2
        = (star (c j) * star (c j)) * (c j * c j) := by ring
    rw [hring, ← star_mul, ← pow_two, hc2, star_sign, hσsq]
  have hxnorm : star (c j) * c j = ((Complex.normSq (c j) : ℝ) : ℂ) := by
    rw [mul_comm]
    exact Complex.mul_conj _
  rw [hxnorm] at hx2
  have hr2 : (Complex.normSq (c j)) ^ 2 = 1 := by exact_mod_cast hx2
  have hnn := Complex.normSq_nonneg (c j)
  have hr1 : Complex.normSq (c j) = 1 := by
    rcases sq_eq_one_iff.mp hr2 with h | h
    · exact h
    · rw [h] at hnn; norm_num at hnn
  rw [hxnorm, hr1, Complex.ofReal_one]

/-- A generator squaring to `1` is Hermitian. -/
private theorem generator_hermitian {n r : ℕ} {a b : Fin r → Fin n → ZMod 2}
    {c : Fin r → ℂ} (hsq : ∀ j, generator a b c j * generator a b c j = 1) (j : Fin r) :
    (generator a b c j)ᴴ = generator a b c j := by
  have hU : (generator a b c j)ᴴ * generator a b c j = 1 := by
    have hP : (pauli (a j) (b j))ᴴ * pauli (a j) (b j) = 1 := by
      rw [pauli_conjTranspose, Matrix.smul_mul, pauli_sq, smul_smul, sign_mul_self, one_smul]
    have hx := generator_star_mul_self hsq j
    show (c j • pauli (a j) (b j))ᴴ * (c j • pauli (a j) (b j)) = 1
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP, hx,
      one_smul]
  calc (generator a b c j)ᴴ = (generator a b c j)ᴴ * 1 := by rw [mul_one]
    _ = (generator a b c j)ᴴ * (generator a b c j * generator a b c j) := by rw [hsq j]
    _ = ((generator a b c j)ᴴ * generator a b c j) * generator a b c j := by rw [mul_assoc]
    _ = generator a b c j := by rw [hU, one_mul]

/-- Commuting generators have vanishing symplectic product. -/
private theorem generator_comm_dots {n r : ℕ} {a b : Fin r → Fin n → ZMod 2}
    {c : Fin r → ℂ} (hsq : ∀ j, generator a b c j * generator a b c j = 1)
    (hcomm : ∀ j k, Commute (generator a b c j) (generator a b c k)) (j k : Fin r) :
    (b j) ⬝ᵥ (a k) = (b k) ⬝ᵥ (a j) := by
  have hcz : ∀ j, c j ≠ 0 := fun j => generator_scalar_ne_zero hsq j
  have hexpand : ∀ x y : Fin r, generator a b c x * generator a b c y
      = (c x * c y) • (sign ((b x) ⬝ᵥ (a y)) • pauli (a x + a y) (b x + b y)) := by
    intro x y
    show (c x • pauli (a x) (b x)) * (c y • pauli (a y) (b y)) = _
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauli_mul]
  have hcommE := (hcomm j k).eq
  rw [hexpand, hexpand, mul_comm (c k) (c j), add_comm (a k) (a j),
    add_comm (b k) (b j)] at hcommE
  have hentry := congrFun (congrFun hcommE (a j + a k)) 0
  simp only [Matrix.smul_apply, smul_eq_mul, pauli, Matrix.of_apply, zero_add,
    eq_self_iff_true, ite_true, dotProduct_zero, sign_zero, mul_one] at hentry
  have hs : c j * c k ≠ 0 := mul_ne_zero (hcz j) (hcz k)
  have hsign : sign ((b j) ⬝ᵥ (a k)) = sign ((b k) ⬝ᵥ (a j)) :=
    mul_left_cancel₀ hs hentry
  exact sign_inj hsign

/-- A generator is the singleton subset product. -/
private theorem generator_eq_groupElem_singleton {n r : ℕ}
    {a b : Fin r → Fin n → ZMod 2} {c : Fin r → ℂ} (j : Fin r) :
    generator a b c j = groupElem a b c {j} := by
  show generator a b c j
    = (List.ofFn fun k : Fin r => if k ∈ ({j} : Finset (Fin r)) then generator a b c k
      else 1).prod
  rw [show (fun k : Fin r => if k ∈ ({j} : Finset (Fin r)) then generator a b c k else 1)
      = (fun k => if k = j then generator a b c k else 1) from ?_]
  · have onehot : ∀ (M : Type) [Monoid M] (m : ℕ) (g : Fin m → M) (t : Fin m),
        (List.ofFn fun k => if k = t then g k else 1).prod = g t := by
      intro M _ m
      induction m with
      | zero => intro g t; exact t.elim0
      | succ m ih =>
        intro g t
        rw [List.ofFn_succ, List.prod_cons]
        rcases Fin.eq_zero_or_eq_succ t with rfl | ⟨t', rfl⟩
        · rw [ite_eq_left rfl]
          have htail : (List.ofFn fun i : Fin m =>
              if i.succ = (0 : Fin (m + 1)) then g i.succ else 1).prod = 1 := by
            apply List.prod_eq_one
            intro x hx
            rw [List.mem_ofFn] at hx
            obtain ⟨i, hi⟩ := hx
            rw [ite_eq_right (Fin.succ_ne_zero i)] at hi
            exact hi.symm
          rw [htail, mul_one]
        · have h0 : (0 : Fin (m + 1)) ≠ t'.succ :=
            fun h => Fin.succ_ne_zero t' h.symm
          have hfun : (fun i : Fin m => if i.succ = t'.succ then g i.succ else 1)
              = (fun i : Fin m => if i = t' then g i.succ else 1) := by
            funext i
            simp only [Fin.succ_inj]
          rw [ite_eq_right h0, hfun, one_mul]
          exact ih _ _
    exact (onehot _ r (fun k => generator a b c k) j).symm
  · funext k
    simp only [Finset.mem_singleton]

/-- The empty subset product is `1`. -/
private theorem groupElem_empty {n r : ℕ} (a b : Fin r → Fin n → ZMod 2)
    (c : Fin r → ℂ) : groupElem a b c ∅ = 1 := by
  have hfun : (fun j : Fin r => if j ∈ (∅ : Finset (Fin r)) then generator a b c j else 1)
      = fun _ => 1 := by
    funext j
    rw [ite_eq_right (Finset.notMem_empty j)]
  show (List.ofFn _).prod = 1
  rw [hfun]
  apply List.prod_eq_one
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨i, hi⟩ := hx
  exact hi.symm

/-- A subset product squares to `1`. -/
private theorem groupElem_self_mul {n r : ℕ} {a b : Fin r → Fin n → ZMod 2}
    {c : Fin r → ℂ} (hsq : ∀ j, generator a b c j * generator a b c j = 1)
    (hcomm : ∀ j k, Commute (generator a b c j) (generator a b c k))
    (T : Finset (Fin r)) : groupElem a b c T * groupElem a b c T = 1 := by
  rw [groupElem_mul hsq hcomm T T, symmDiff_self]
  exact groupElem_empty a b c

/-- Splitting a sum over `Fin (n+1)` at `0`. -/
private theorem sum_split_succ {n : ℕ} {M : Type*} [AddCommMonoid M] (F : Fin (n + 1) → M)
    (T : Finset (Fin (n + 1))) (T' : Finset (Fin n))
    (hmem : ∀ i : Fin n, i ∈ T' ↔ i.succ ∈ T) :
    (∑ j ∈ T, F j) = (if (0 : Fin (n + 1)) ∈ T then F 0 else 0)
      + ∑ i ∈ T', F i.succ := by
  have h1 : (∑ j ∈ T, F j) = ∑ j : Fin (n + 1), (if j ∈ T then F j else 0) := by
    have hsub : (∑ j ∈ T, (if j ∈ T then F j else 0))
        = ∑ j : Fin (n + 1), (if j ∈ T then F j else 0) :=
      Finset.sum_subset (Finset.subset_univ T) (fun j _ hj => ite_eq_right hj)
    rw [← hsub]
    exact Finset.sum_congr rfl (fun j hj => (ite_eq_left hj).symm)
  rw [h1, Fin.sum_univ_succ]
  have hfun : (fun i : Fin n => if i.succ ∈ T then F i.succ else 0)
      = (fun i => if i ∈ T' then F i.succ else 0) := by
    funext i
    simp only [← hmem i]
  rw [hfun]
  have hcongr : (∑ i : Fin n, (if i ∈ T' then F i.succ else 0)) = ∑ i ∈ T', F i.succ := by
    have hsub : (∑ i ∈ T', (if i ∈ T' then F i.succ else 0))
        = ∑ i : Fin n, (if i ∈ T' then F i.succ else 0) :=
      Finset.sum_subset (Finset.subset_univ T') (fun i _ hi => ite_eq_right hi)
    rw [← hsub]
    exact Finset.sum_congr rfl (fun i hi => ite_eq_left hi)
  rw [hcongr]

/-- A subset product is a nonzero scalar times the summed Pauli. -/
private theorem groupElem_eq_smul_pauli {n r : ℕ} {a b : Fin r → Fin n → ZMod 2}
    {c : Fin r → ℂ} (hsq : ∀ j, generator a b c j * generator a b c j = 1)
    (hcomm : ∀ j k, Commute (generator a b c j) (generator a b c k))
    (T : Finset (Fin r)) :
    ∃ σ : ℂ, σ ≠ 0 ∧ groupElem a b c T
      = σ • pauli (∑ j ∈ T, a j) (∑ j ∈ T, b j) := by
  induction r with
  | zero =>
    have hTe : T = ∅ := by
      ext j
      exact Fin.elim0 j
    refine ⟨1, one_ne_zero, ?_⟩
    rw [hTe, groupElem_empty, Finset.sum_empty, Finset.sum_empty, pauli_zero_zero, one_smul]
  | succ n ih =>
    set T' : Finset (Fin n) := Finset.univ.filter (fun i => i.succ ∈ T) with hT'def
    have hmem : ∀ i : Fin n, i ∈ T' ↔ i.succ ∈ T := by
      intro i
      simp [hT'def]
    have hsq' : ∀ i : Fin n, generator (fun i => a i.succ) (fun i => b i.succ)
        (fun i => c i.succ) i * generator (fun i => a i.succ) (fun i => b i.succ)
        (fun i => c i.succ) i = 1 := fun i => by simpa [generator] using hsq i.succ
    have hcomm' : ∀ i k : Fin n,
        Commute (generator (fun i => a i.succ) (fun i => b i.succ) (fun i => c i.succ) i)
          (generator (fun i => a i.succ) (fun i => b i.succ) (fun i => c i.succ) k) :=
      fun i k => by simpa only [generator] using hcomm i.succ k.succ
    obtain ⟨σ', hσ'ne, hσ'eq⟩ := ih (a := fun i => a i.succ) (b := fun i => b i.succ) (c := fun i => c i.succ) hsq' hcomm' T'
    have htail : (List.ofFn fun i : Fin n => if i.succ ∈ T then generator a b c i.succ
        else 1).prod
        = groupElem (fun i => a i.succ) (fun i => b i.succ) (fun i => c i.succ) T' := by
      have hfun : (fun i : Fin n => if i.succ ∈ T then generator a b c i.succ else 1)
          = (fun i => if i ∈ T' then generator (fun i => a i.succ) (fun i => b i.succ)
            (fun i => c i.succ) i else 1) := by
        funext i
        by_cases h : i.succ ∈ T
        · simp only [ite_eq_left h, ite_eq_left ((hmem i).mpr h), generator]
        · simp only [ite_eq_right h, ite_eq_right (fun hi => h ((hmem i).mp hi))]
      unfold groupElem
      rw [hfun]
    have hsumA : (∑ j ∈ T, a j) = (if (0 : Fin (n + 1)) ∈ T then a 0 else 0)
        + ∑ i ∈ T', a i.succ :=
      sum_split_succ a T T' hmem
    have hsumB : (∑ j ∈ T, b j) = (if (0 : Fin (n + 1)) ∈ T then b 0 else 0)
        + ∑ i ∈ T', b i.succ :=
      sum_split_succ b T T' hmem
    have hhead : groupElem a b c T
        = (if (0 : Fin (n + 1)) ∈ T then generator a b c 0 else 1)
          * (List.ofFn fun i : Fin n => if i.succ ∈ T then generator a b c i.succ
            else 1).prod := by
      unfold groupElem
      simp only [List.ofFn_succ, List.prod_cons]
    by_cases h0T : (0 : Fin (n + 1)) ∈ T
    · refine ⟨(c 0 * σ') * sign ((b 0) ⬝ᵥ (∑ i ∈ T', a i.succ)), ?_, ?_⟩
      · exact mul_ne_zero (mul_ne_zero (generator_scalar_ne_zero hsq 0) hσ'ne)
          (sign_ne_zero _)
      · rw [hhead, ite_eq_left h0T, htail, hσ'eq]
        simp only [generator]
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauli_mul, smul_smul, hsumA, hsumB,
          ite_eq_left h0T, ite_eq_left h0T]
    · refine ⟨σ', hσ'ne, ?_⟩
      rw [hhead, ite_eq_right h0T, htail, hσ'eq, one_mul, hsumA, hsumB,
        ite_eq_right h0T, ite_eq_right h0T, zero_add, zero_add]

/-- A sum of scaled pairs splits into the pair of sums. -/
private theorem pair_sum_smul {n r : ℕ} (a b : Fin r → Fin n → ZMod 2)
    (g : Fin r → ZMod 2) (S : Finset (Fin r)) :
    ∑ j ∈ S, g j • (a j, b j) = (∑ j ∈ S, g j • a j, ∑ j ∈ S, g j • b j) := by
  induction S using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Finset.sum_empty]; rfl
  | insert i t hit ih =>
    have hsmul : ∀ (x y : Fin n → ZMod 2) (c : ZMod 2),
        c • (x, y) = (c • x, c • y) := fun _ _ _ => rfl
    rw [Finset.sum_insert hit, Finset.sum_insert hit, Finset.sum_insert hit, hsmul, ih,
      Prod.mk_add_mk]

/-- Vanishing generator sums force the index set to be empty, by independence. -/
private theorem eq_empty_of_sums_eq_zero {n r : ℕ} (a b : Fin r → Fin n → ZMod 2)
    (hind : LinearIndependent (ZMod 2) fun j => (a j, b j))
    (T : Finset (Fin r)) (hA : ∑ j ∈ T, a j = 0) (hB : ∑ j ∈ T, b j = 0) : T = ∅ := by
  have hsum : ∑ j ∈ T, (fun _ => (1 : ZMod 2)) j • (a j, b j) = 0 := by
    rw [pair_sum_smul]
    simp only [one_smul]
    rw [hA, hB]
    rfl
  have hall : ∀ i ∈ T, (1 : ZMod 2) = 0 := by
    intro i hi
    exact linearIndependent_iff'.mp hind T (fun _ => (1 : ZMod 2)) hsum i hi
  exact Finset.eq_empty_of_forall_notMem fun i hi => one_ne_zero (hall i hi)

/-- A subset product equal to `1` has vanishing generator sums. -/
private theorem sums_eq_zero_of_groupElem_eq_one {n r : ℕ} {a b : Fin r → Fin n → ZMod 2}
    {c : Fin r → ℂ} (hsq : ∀ j, generator a b c j * generator a b c j = 1)
    (hcomm : ∀ j k, Commute (generator a b c j) (generator a b c k))
    (T : Finset (Fin r)) (h1 : groupElem a b c T = 1) :
    ∑ j ∈ T, a j = 0 ∧ ∑ j ∈ T, b j = 0 := by
  classical
  obtain ⟨σ, hσne, hσeq⟩ := groupElem_eq_smul_pauli hsq hcomm T
  rw [hσeq] at h1
  have hentry := congrFun (congrFun h1 (∑ j ∈ T, a j)) 0
  simp only [Matrix.smul_apply, smul_eq_mul, pauli, Matrix.of_apply, zero_add,
    eq_self_iff_true, ite_true, dotProduct_zero, sign_zero, mul_one,
    Matrix.one_apply] at hentry
  by_cases hA0 : (∑ j ∈ T, a j) = 0
  · rw [ite_eq_left hA0] at hentry
    rw [hA0, hentry, one_smul] at h1
    have hBv : ∀ v : Fin n → ZMod 2, sign ((∑ j ∈ T, b j) ⬝ᵥ v) = 1 := by
      intro v
      have hv := congrFun (congrFun h1 v) v
      simp only [pauli, Matrix.of_apply, add_zero, eq_self_iff_true, ite_true,
        Matrix.one_apply] at hv
      exact hv
    have hB0 : (∑ j ∈ T, b j) = 0 := by
      have hdot : ∀ v : Fin n → ZMod 2, (∑ j ∈ T, b j) ⬝ᵥ v = 0 := by
        intro v
        apply sign_inj
        rw [hBv v]
        exact sign_zero.symm
      funext i
      have hi := hdot (fun j => if j = i then 1 else 0)
      have hBe : (∑ j ∈ T, b j) ⬝ᵥ (fun j => if j = i then (1 : ZMod 2) else 0)
          = (∑ j ∈ T, b j) i := by
        simp only [dotProduct]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          simp [hji]
        · intro hj
          exact absurd (Finset.mem_univ i) hj
      rw [hBe] at hi
      simpa using hi
    exact ⟨hA0, hB0⟩
  · rw [ite_eq_right hA0] at hentry
    exact absurd hentry hσne

/-- A subset product commutes with `y` when every generator does. -/
private theorem commute_groupElem_right {n r : ℕ} {a b : Fin r → Fin n → ZMod 2}
    {c : Fin r → ℂ} (y : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (T : Finset (Fin r)) (h : ∀ j, Commute (generator a b c j) y) :
    Commute (groupElem a b c T) y := by
  show Commute (List.ofFn fun j => if j ∈ T then generator a b c j else 1).prod y
  refine Commute.list_prod_left _ _ fun x hx => ?_
  rw [List.mem_ofFn] at hx
  obtain ⟨j, rfl⟩ := hx
  by_cases hj : j ∈ T
  · rw [ite_eq_left hj]
    exact h j
  · rw [ite_eq_right hj]
    exact Commute.one_left y
/-- A subset product of Hermitian generators is Hermitian. -/
private theorem groupElem_hermitian {n r : ℕ} {a b : Fin r → Fin n → ZMod 2}
    {c : Fin r → ℂ} (hsq : ∀ j, generator a b c j * generator a b c j = 1)
    (hcomm : ∀ j k, Commute (generator a b c j) (generator a b c k))
    (T : Finset (Fin r)) : (groupElem a b c T)ᴴ = groupElem a b c T := by
  induction r with
  | zero =>
    have hTe : T = ∅ := by
      ext j
      exact Fin.elim0 j
    rw [hTe, groupElem_empty]
    exact Matrix.conjTranspose_one
  | succ n ih =>
    set T' : Finset (Fin n) := Finset.univ.filter (fun i => i.succ ∈ T) with hT'def
    have hmem : ∀ i : Fin n, i ∈ T' ↔ i.succ ∈ T := by
      intro i
      simp [hT'def]
    have htail : (List.ofFn fun i : Fin n => if i.succ ∈ T then generator a b c i.succ
        else 1).prod
        = groupElem (fun i => a i.succ) (fun i => b i.succ) (fun i => c i.succ) T' := by
      have hfun : (fun i : Fin n => if i.succ ∈ T then generator a b c i.succ else 1)
          = (fun i => if i ∈ T' then generator (fun i => a i.succ) (fun i => b i.succ)
            (fun i => c i.succ) i else 1) := by
        funext i
        simp only [hmem i, generator]
      unfold groupElem
      rw [hfun]
    have hhead : groupElem a b c T
        = (if (0 : Fin (n + 1)) ∈ T then generator a b c 0 else 1)
          * (List.ofFn fun i : Fin n => if i.succ ∈ T then generator a b c i.succ
            else 1).prod := by
      unfold groupElem
      simp only [List.ofFn_succ, List.prod_cons]
    have hIH := @ih (fun i => a i.succ) (fun i => b i.succ) (fun i => c i.succ)
      (fun i => hsq i.succ) (fun i k => hcomm i.succ k.succ) T'
    rw [hhead, Matrix.conjTranspose_mul, htail, hIH]
    by_cases h0T : (0 : Fin (n + 1)) ∈ T
    · rw [ite_eq_left h0T, generator_hermitian hsq 0]
      exact (commute_groupElem_right _ _ (fun i => hcomm i.succ 0)).eq
    · rw [ite_eq_right h0T, Matrix.conjTranspose_one, mul_one, one_mul]

/-- Left multiplication by a group element permutes the group sum. -/
private theorem sum_mul_mem_stabilizerGroup {n r : ℕ} {a b : Fin r → Fin n → ZMod 2}
    {c : Fin r → ℂ} (hsq : ∀ j, generator a b c j * generator a b c j = 1)
    (hcomm : ∀ j k, Commute (generator a b c j) (generator a b c k))
    (s : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (hs : s ∈ stabilizerGroup a b c) :
    (∑ t ∈ stabilizerGroup a b c, s * t) = ∑ u ∈ stabilizerGroup a b c, u := by
  classical
  have hG : stabilizerGroup a b c = Finset.univ.image (groupElem a b c) := rfl
  obtain ⟨S₀, _, rfl⟩ := Finset.mem_image.mp (hG ▸ hs)
  refine Finset.sum_bij (fun t _ => groupElem a b c S₀ * t) ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp (hG ▸ ht)
    rw [hG, Finset.mem_image]
    exact ⟨symmDiff S₀ T, Finset.mem_univ _, (groupElem_mul hsq hcomm S₀ T).symm⟩
  · intro t₁ ht₁ t₂ ht₂ h12
    have hss : groupElem a b c S₀ * groupElem a b c S₀ = 1 :=
      groupElem_self_mul hsq hcomm S₀
    have h : groupElem a b c S₀ * (groupElem a b c S₀ * t₁)
        = groupElem a b c S₀ * (groupElem a b c S₀ * t₂) :=
      congrArg (groupElem a b c S₀ * ·) h12
    rw [← mul_assoc, ← mul_assoc, hss, one_mul, one_mul] at h
    exact h
  · intro u hu
    refine ⟨groupElem a b c S₀ * u, ?_, ?_⟩
    · obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp (hG ▸ hu)
      rw [hG, Finset.mem_image]
      exact ⟨symmDiff S₀ T, Finset.mem_univ _, (groupElem_mul hsq hcomm S₀ T).symm⟩
    · show groupElem a b c S₀ * (groupElem a b c S₀ * u) = u
      rw [← mul_assoc, groupElem_self_mul hsq hcomm S₀, one_mul]
  · intro t ht
    rfl

/-- A product of factors fixing `x` fixes `x`. -/
private theorem mulVec_ofFn_prod_fix {n r : ℕ}
    (f : Fin r → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (x : (Fin n → ZMod 2) → ℂ) (h : ∀ j, f j *ᵥ x = x) :
    (List.ofFn f).prod *ᵥ x = x := by
  induction r with
  | zero => rw [List.ofFn_zero, List.prod_nil, Matrix.one_mulVec]
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [← Matrix.mulVec_mulVec, ih _ (fun i => h i.succ), h 0]

/-- On the kernel of the `X` parts, the `Z` combination is orthogonal to the range. -/
private theorem orth_sumComb {n r : ℕ} {a b : Fin r → Fin n → ZMod 2} {c : Fin r → ℂ}
    (hsq : ∀ j, generator a b c j * generator a b c j = 1)
    (hcomm : ∀ j k, Commute (generator a b c j) (generator a b c k))
    (u : Fin r → ZMod 2) (hu : Fintype.linearCombination (ZMod 2) a u = 0) (d : Fin r → ZMod 2) :
    Fintype.linearCombination (ZMod 2) b u ⬝ᵥ Fintype.linearCombination (ZMod 2) a d = 0 := by
  have hcomm' := generator_comm_dots hsq hcomm
  simp only [Fintype.linearCombination_apply]
  rw [sum_dotProduct]
  simp only [dotProduct_sum]
  have hterm : ∀ j k : Fin r, (u j • b j) ⬝ᵥ (d k • a k)
      = d k * (u j * ((b k) ⬝ᵥ (a j))) := by
    intro j k
    rw [smul_dotProduct, dotProduct_smul, hcomm' j k, smul_eq_mul, smul_eq_mul]
    ring
  simp only [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k _
  have hinner : (∑ j, d k * (u j * ((b k) ⬝ᵥ (a j))))
      = d k * ((b k) ⬝ᵥ (Fintype.linearCombination (ZMod 2) a u)) := by
    rw [Fintype.linearCombination_apply]
    rw [dotProduct_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dotProduct_smul, smul_eq_mul]
  rw [hinner, hu, dotProduct_zero, mul_zero]

/-- The `Z` combination, from the kernel of the `X` parts to the dual of the range. -/
private noncomputable def resB {n r : ℕ} {a b : Fin r → Fin n → ZMod 2} {c : Fin r → ℂ}
    (hsq : ∀ j, generator a b c j * generator a b c j = 1)
    (hcomm : ∀ j k, Commute (generator a b c j) (generator a b c k)) :
    LinearMap.ker (Fintype.linearCombination (ZMod 2) a) →ₗ[ZMod 2]
      Cslib.CodingTheory.LinearCode.dual (LinearMap.range (Fintype.linearCombination (ZMod 2) a)) where
  toFun z := ⟨Fintype.linearCombination (ZMod 2) b z.1, by
    have hz : Fintype.linearCombination (ZMod 2) a z.1 = 0 := LinearMap.mem_ker.mp z.2
    rw [Cslib.CodingTheory.LinearCode.mem_dual]
    intro s hs
    obtain ⟨d, rfl⟩ := LinearMap.mem_range.mp hs
    exact orth_sumComb hsq hcomm z.1 hz d⟩
  map_add' z w := Subtype.ext (map_add (Fintype.linearCombination (ZMod 2) b) z.1 w.1)
  map_smul' t z := Subtype.ext (map_smul (Fintype.linearCombination (ZMod 2) b) t z.1)

/-- A nontrivial Pauli operator is traceless. -/
private theorem trace_pauli_eq_zero_of_ne {n : ℕ} (A B : Fin n → ZMod 2)
    (h : A ≠ 0 ∨ B ≠ 0) : (pauli A B).trace = 0 := by
  classical
  have htr : (pauli A B).trace = ∑ v, (if v = v + A then sign (B ⬝ᵥ v) else 0) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.diag_apply, pauli, Matrix.of_apply]
  have hcase : ∀ A' : Fin n → ZMod 2, A' ≠ 0 →
      (∑ v, (if v = v + A' then sign (B ⬝ᵥ v) else 0)) = 0 := by
    intro A' hA'
    have hneg : ∀ v : Fin n → ZMod 2, ¬ v = v + A' := by
      intro v hcon
      apply hA'
      have hAA : v + A' = v + 0 := by
        rw [add_zero]
        exact hcon.symm
      exact add_left_cancel_iff.mp hAA
    exact Finset.sum_eq_zero (fun v _ => ite_eq_right (hneg v))
  rw [htr]
  rcases h with hA | hB
  · exact hcase A hA
  · by_cases hA0 : A = 0
    · subst hA0
      have hif : ∀ v : Fin n → ZMod 2, (if v = v + 0 then sign (B ⬝ᵥ v) else 0)
          = sign (B ⬝ᵥ v) := by
        intro v
        rw [add_zero, ite_eq_left rfl]
      simp only [hif]
      have hex : ∃ c ∈ (⊤ : Cslib.CodingTheory.LinearCode (ZMod 2) (Fin n)),
          c ⬝ᵥ B ≠ 0 := by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hB
        refine ⟨(fun j => if j = i then 1 else 0), Submodule.mem_top, ?_⟩
        have hce : (fun j => if j = i then (1 : ZMod 2) else 0) ⬝ᵥ B = B i := by
          simp only [dotProduct]
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji
            simp [hji]
          · intro hj
            exact absurd (Finset.mem_univ i) hj
        rw [hce]
        simpa using hi
      have hsum := sum_sign_eq_zero
        (⊤ : Cslib.CodingTheory.LinearCode (ZMod 2) (Fin n)) hex
      have hcongr : ∀ v : Fin n → ZMod 2, sign (B ⬝ᵥ v)
          = (if v ∈ (⊤ : Cslib.CodingTheory.LinearCode (ZMod 2) (Fin n))
            then sign (v ⬝ᵥ B) else 0) := by
        intro v
        rw [ite_eq_left Submodule.mem_top, dotProduct_comm]
      rw [Finset.sum_congr rfl (fun v _ => hcongr v)]
      exact hsum
    · exact hcase A hA0

/-- Independent generators give `2 ^ r` distinct products. -/
theorem card_stabilizerGroup {n r : ℕ} {a b : Fin r → Fin n → ZMod 2} {c : Fin r → ℂ}
    (hsq : ∀ j, generator a b c j * generator a b c j = 1)
    (hcomm : ∀ j k, Commute (generator a b c j) (generator a b c k))
    (hind : LinearIndependent (ZMod 2) fun j => (a j, b j)) :
    (stabilizerGroup a b c).card = 2 ^ r := by
  classical
  have hG : stabilizerGroup a b c = Finset.univ.image (groupElem a b c) := rfl
  have hinj : Function.Injective (groupElem a b c) := by
    intro T T' hTT'
    have hsymm : groupElem a b c (symmDiff T T') = 1 := by
      have h : groupElem a b c T * groupElem a b c T'
          = groupElem a b c T' * groupElem a b c T' :=
        congrArg (· * groupElem a b c T') hTT'
      rw [groupElem_mul hsq hcomm T T', groupElem_self_mul hsq hcomm T'] at h
      exact h
    have hSe : symmDiff T T' = ∅ := by
      obtain ⟨hA, hB⟩ := sums_eq_zero_of_groupElem_eq_one hsq hcomm _ hsymm
      exact eq_empty_of_sums_eq_zero _ _ hind _ hA hB
    exact Finset.symmDiff_eq_empty.mp hSe
  rw [hG, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_finset,
    Fintype.card_fin]

/-- The code projector is Hermitian. -/
theorem conjTranspose_codeProjector {n r : ℕ} {a b : Fin r → Fin n → ZMod 2} {c : Fin r → ℂ}
    (hsq : ∀ j, generator a b c j * generator a b c j = 1)
    (hcomm : ∀ j k, Commute (generator a b c j) (generator a b c k)) :
    (codeProjector a b c)ᴴ = codeProjector a b c := by
  classical
  have hG : stabilizerGroup a b c = Finset.univ.image (groupElem a b c) := rfl
  have hH : ∀ s ∈ stabilizerGroup a b c, sᴴ = s := by
    intro s hs
    rw [hG] at hs
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hs
    exact groupElem_hermitian hsq hcomm T
  have hstar : star (((stabilizerGroup a b c).card : ℂ)⁻¹)
      = ((stabilizerGroup a b c).card : ℂ)⁻¹ := by
    rw [star_inv₀, star_natCast]
  have hP : codeProjector a b c
      = ((stabilizerGroup a b c).card : ℂ)⁻¹ • ∑ s ∈ stabilizerGroup a b c, s := rfl
  rw [hP, Matrix.conjTranspose_smul, hstar, Matrix.conjTranspose_sum]
  congr 1
  exact Finset.sum_congr rfl (fun s hs => hH s hs)

/-- The code projector is idempotent. -/
theorem codeProjector_mul_self {n r : ℕ} {a b : Fin r → Fin n → ZMod 2} {c : Fin r → ℂ}
    (hsq : ∀ j, generator a b c j * generator a b c j = 1)
    (hcomm : ∀ j k, Commute (generator a b c j) (generator a b c k)) :
    codeProjector a b c * codeProjector a b c = codeProjector a b c := by
  classical
  have hG : stabilizerGroup a b c = Finset.univ.image (groupElem a b c) := rfl
  have hmem1 : groupElem a b c ∅ ∈ stabilizerGroup a b c := by
    rw [hG]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hcard : (stabilizerGroup a b c).card ≠ 0 :=
    ne_of_gt (Finset.card_pos.mpr ⟨_, hmem1⟩)
  have hN : ((stabilizerGroup a b c).card : ℂ) ≠ 0 := by exact_mod_cast hcard
  have hP : codeProjector a b c
      = ((stabilizerGroup a b c).card : ℂ)⁻¹ • ∑ s ∈ stabilizerGroup a b c, s := rfl
  have hSS : (∑ s ∈ stabilizerGroup a b c, s) * (∑ t ∈ stabilizerGroup a b c, t)
      = (stabilizerGroup a b c).card • (∑ u ∈ stabilizerGroup a b c, u) := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    trans ∑ s ∈ stabilizerGroup a b c, ∑ u ∈ stabilizerGroup a b c, u
    · exact Finset.sum_congr rfl (fun s hs => sum_mul_mem_stabilizerGroup hsq hcomm s hs)
    · rw [Finset.sum_const]
  rw [hP, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hSS, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul]
  congr 1
  calc (((stabilizerGroup a b c).card : ℂ)⁻¹ * ((stabilizerGroup a b c).card : ℂ)⁻¹)
          * (stabilizerGroup a b c).card
        = ((stabilizerGroup a b c).card : ℂ)⁻¹
          * (((stabilizerGroup a b c).card : ℂ)⁻¹ * (stabilizerGroup a b c).card) := by
          rw [mul_assoc]
    _ = ((stabilizerGroup a b c).card : ℂ)⁻¹ * 1 := by rw [inv_mul_cancel₀ hN]
    _ = ((stabilizerGroup a b c).card : ℂ)⁻¹ := mul_one _

/-- The code projector projects onto the code space. -/
theorem range_toLin'_codeProjector {n r : ℕ} {a b : Fin r → Fin n → ZMod 2} {c : Fin r → ℂ}
    (hsq : ∀ j, generator a b c j * generator a b c j = 1)
    (hcomm : ∀ j k, Commute (generator a b c j) (generator a b c k)) :
    LinearMap.range (Matrix.toLin' (codeProjector a b c)) = codeSpace a b c := by
  classical
  have hG : stabilizerGroup a b c = Finset.univ.image (groupElem a b c) := rfl
  have hP : codeProjector a b c
      = ((stabilizerGroup a b c).card : ℂ)⁻¹ • ∑ s ∈ stabilizerGroup a b c, s := rfl
  have hmem1 : groupElem a b c ∅ ∈ stabilizerGroup a b c := by
    rw [hG]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hN : ((stabilizerGroup a b c).card : ℂ) ≠ 0 := by
    have hcard : (stabilizerGroup a b c).card ≠ 0 :=
      ne_of_gt (Finset.card_pos.mpr ⟨_, hmem1⟩)
    exact_mod_cast hcard
  have hMjP : ∀ j : Fin r,
      generator a b c j * codeProjector a b c = codeProjector a b c := by
    intro j
    have hMjmem : generator a b c j ∈ stabilizerGroup a b c := by
      rw [hG, generator_eq_groupElem_singleton, Finset.mem_image]
      exact ⟨{j}, Finset.mem_univ _, rfl⟩
    rw [hP, Matrix.mul_smul, Finset.mul_sum,
      sum_mul_mem_stabilizerGroup hsq hcomm _ hMjmem]
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    show Matrix.toLin' (codeProjector a b c) x ∈ codeSpace a b c
    show Matrix.toLin' (codeProjector a b c) x ∈
      ⨅ j, LinearMap.ker (Matrix.toLin' (generator a b c j) - LinearMap.id)
    rw [Submodule.mem_iInf]
    intro j
    rw [LinearMap.mem_ker, LinearMap.sub_apply]
    have hcomp : Matrix.toLin' (generator a b c j) (Matrix.toLin' (codeProjector a b c) x)
        = Matrix.toLin' (codeProjector a b c) x := by
      rw [← Matrix.toLin'_mul_apply, hMjP j]
    rw [hcomp]
    have hid : (LinearMap.id : ((Fin n → ZMod 2) → ℂ) →ₗ[ℂ]
        ((Fin n → ZMod 2) → ℂ)) (Matrix.toLin' (codeProjector a b c) x)
        = Matrix.toLin' (codeProjector a b c) x := rfl
    rw [hid, sub_self]
  · intro hy
    have hfix : ∀ j : Fin r, Matrix.toLin' (generator a b c j) y = y := by
      intro j
      have hker : y ∈ LinearMap.ker (Matrix.toLin' (generator a b c j) - LinearMap.id) := by
        have hx : y ∈ ⨅ k, LinearMap.ker (Matrix.toLin' (generator a b c k)
          - LinearMap.id) := hy
        exact ((Submodule.mem_iInf _).mp hx) j
      have h0 := LinearMap.mem_ker.mp hker
      simp only [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h0
      exact h0
    have hsfix : ∀ s ∈ stabilizerGroup a b c, s *ᵥ y = y := by
      intro s hs
      rw [hG] at hs
      obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hs
      have hfac : ∀ j : Fin r, (if j ∈ T then generator a b c j else 1) *ᵥ y = y := by
        intro j
        by_cases hj : j ∈ T
        · rw [ite_eq_left hj, ← Matrix.toLin'_apply]
          exact hfix j
        · rw [ite_eq_right hj]
          exact Matrix.one_mulVec y
      exact mulVec_ofFn_prod_fix (fun j => if j ∈ T then generator a b c j else 1) y hfac
    have hPy : Matrix.toLin' (codeProjector a b c) y = y := by
      rw [hP, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.sum_mulVec]
      trans ((stabilizerGroup a b c).card : ℂ)⁻¹ • ∑ s ∈ stabilizerGroup a b c, y
      · congr 1
        exact Finset.sum_congr rfl (fun s hs => hsfix s hs)
      · rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN,
          one_smul]
    rw [← hPy]
    exact LinearMap.mem_range.mpr ⟨y, rfl⟩

/-- Commuting independent signed Pauli generators number at most `n`. -/
theorem le_of_linearIndependent {n r : ℕ} {a b : Fin r → Fin n → ZMod 2} {c : Fin r → ℂ}
    (hsq : ∀ j, generator a b c j * generator a b c j = 1)
    (hcomm : ∀ j k, Commute (generator a b c j) (generator a b c k))
    (hind : LinearIndependent (ZMod 2) fun j => (a j, b j)) :
    r ≤ n := by
  classical
  have hinjB : Function.Injective (resB (a := a) (b := b) (c := c) hsq hcomm) := by
    intro z w hzw
    have hB : Fintype.linearCombination (ZMod 2) b z.1 = Fintype.linearCombination (ZMod 2) b w.1 := congrArg Subtype.val hzw
    have hAsub : Fintype.linearCombination (ZMod 2) a (z.1 - w.1) = 0 := by
      rw [map_sub, LinearMap.mem_ker.mp z.2, LinearMap.mem_ker.mp w.2, sub_self]
    have hBsub : Fintype.linearCombination (ZMod 2) b (z.1 - w.1) = 0 := by
      rw [map_sub, hB, sub_self]
    have hsum0 : ∑ j, (z.1 - w.1) j • (a j, b j) = 0 := by
      have hA' : (∑ j, (z.1 - w.1) j • a j) = 0 := hAsub
      have hB' : (∑ j, (z.1 - w.1) j • b j) = 0 := hBsub
      rw [pair_sum_smul _ _ _ Finset.univ, hA', hB']
      rfl
    have hindep : ∀ i, (z.1 - w.1) i = 0 :=
      fun i => Fintype.linearIndependent_iff.mp hind _ hsum0 i
    have h0 : z.1 - w.1 = 0 := funext hindep
    have hzw1 : z.1 = w.1 := sub_eq_zero.mp h0
    exact Subtype.ext hzw1
  have hfrange : Module.finrank (ZMod 2)
        (LinearMap.range (resB (a := a) (b := b) (c := c) hsq hcomm))
      = Module.finrank (ZMod 2) (LinearMap.ker (Fintype.linearCombination (ZMod 2) a)) :=
    LinearMap.finrank_range_of_inj hinjB
  have hle1 : Module.finrank (ZMod 2) (LinearMap.ker (Fintype.linearCombination (ZMod 2) a))
      ≤ Module.finrank (ZMod 2)
        (Cslib.CodingTheory.LinearCode.dual (LinearMap.range (Fintype.linearCombination (ZMod 2) a))) := by
    rw [← hfrange]
    exact Submodule.finrank_le _
  have hrn := LinearMap.finrank_range_add_finrank_ker (Fintype.linearCombination (ZMod 2) a)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrn
  have hdual := Cslib.CodingTheory.LinearCode.finrank_add_finrank_dual
    (LinearMap.range (Fintype.linearCombination (ZMod 2) a))
  rw [Fintype.card_fin] at hdual
  omega

/-- The trace of the code projector is `2 ^ (n - r)`. -/
theorem trace_codeProjector {n r : ℕ} {a b : Fin r → Fin n → ZMod 2} {c : Fin r → ℂ}
    (hsq : ∀ j, generator a b c j * generator a b c j = 1)
    (hcomm : ∀ j k, Commute (generator a b c j) (generator a b c k))
    (hind : LinearIndependent (ZMod 2) fun j => (a j, b j)) :
    (codeProjector a b c).trace = (2 : ℂ) ^ (n - r) := by
  classical
  have hG : stabilizerGroup a b c = Finset.univ.image (groupElem a b c) := rfl
  have hcard : (stabilizerGroup a b c).card = 2 ^ r := card_stabilizerGroup hsq hcomm hind
  have hle : r ≤ n := le_of_linearIndependent hsq hcomm hind
  have hP : codeProjector a b c
      = ((stabilizerGroup a b c).card : ℂ)⁻¹ • ∑ s ∈ stabilizerGroup a b c, s := rfl
  have hcard2 : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := Fin n → ZMod 2),
      ZMod.card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have htr : ∀ s ∈ stabilizerGroup a b c, s.trace = if s = 1 then (2 : ℂ) ^ n else 0 := by
    intro s hs
    rw [hG] at hs
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hs
    by_cases hT : T = ∅
    · subst hT
      rw [groupElem_empty, ite_eq_left rfl, Matrix.trace_one, hcard2]
      norm_cast
    · have hne : groupElem a b c T ≠ 1 := by
        intro hcon
        apply hT
        obtain ⟨hA, hB⟩ := sums_eq_zero_of_groupElem_eq_one hsq hcomm T hcon
        exact eq_empty_of_sums_eq_zero _ _ hind T hA hB
      rw [ite_eq_right hne]
      obtain ⟨σ, hσne, hσeq⟩ := groupElem_eq_smul_pauli hsq hcomm T
      have hAB : (∑ j ∈ T, a j) ≠ 0 ∨ (∑ j ∈ T, b j) ≠ 0 := by
        by_contra hcon
        simp only [not_or, not_not] at hcon
        exact hT (eq_empty_of_sums_eq_zero _ _ hind T hcon.1 hcon.2)
      have htr0 : (pauli (∑ j ∈ T, a j) (∑ j ∈ T, b j)).trace = 0 :=
        trace_pauli_eq_zero_of_ne _ _ hAB
      rw [hσeq, Matrix.trace_smul, htr0, smul_zero]
  have h1mem : (1 : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
      ∈ stabilizerGroup a b c := by
    have h1e : (1 : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
        = groupElem a b c ∅ :=
      (groupElem_empty _ _ _).symm
    rw [h1e, hG]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hsum : ∑ s ∈ stabilizerGroup a b c, s.trace = (2 : ℂ) ^ n := by
    trans ∑ s ∈ stabilizerGroup a b c, (if s = 1 then (2 : ℂ) ^ n else 0)
    · exact Finset.sum_congr rfl (fun s hs => htr s hs)
    · rw [Finset.sum_eq_single 1]
      · rw [ite_eq_left rfl]
      · intro s _ hs1
        exact ite_eq_right hs1
      · intro hcon
        exact absurd h1mem hcon
  have h2n : (2 : ℂ) ^ n = (2 : ℂ) ^ (n - r) * (2 : ℂ) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  have hcast : (((2 ^ r : ℕ)) : ℂ) = (2 : ℂ) ^ r := by norm_cast
  have hY : (2 : ℂ) ^ r ≠ 0 := pow_ne_zero _ two_ne_zero
  simp only [hP, Matrix.trace_smul, Matrix.trace_sum, hsum, smul_eq_mul, hcard, hcast]
  rw [h2n, mul_comm ((2 : ℂ) ^ (n - r)) ((2 : ℂ) ^ r), ← mul_assoc, inv_mul_cancel₀ hY,
    one_mul]

/-- **Dimension of a stabilizer code.** Let `M j = c j • X^{a j} Z^{b j}` (`j < r`) be Pauli
operators on `n` qubits, up to scalars, with `M j * M j = 1`, pairwise commuting, and with
`(a j, b j)` linearly independent over `F₂`. Then the common `+1` eigenspace
`{ψ | M j ψ = ψ for all j}` has dimension `2 ^ (n - r)` (J. Preskill, Ph219 lecture notes,
Chapter 7, Section 7.9.1; D. Gottesman, PhD thesis (1997), Section 3.2). -/
theorem finrank_stabilizerCode {n r : ℕ} (a b : Fin r → Fin n → ZMod 2) (c : Fin r → ℂ)
    (hsq : ∀ j, (c j • pauli (a j) (b j)) * (c j • pauli (a j) (b j)) = 1)
    (hcomm : ∀ j k, Commute (c j • pauli (a j) (b j)) (c k • pauli (a k) (b k)))
    (hind : LinearIndependent (ZMod 2) fun j => (a j, b j)) :
    Module.finrank ℂ
        (⨅ j, LinearMap.ker (Matrix.toLin' (c j • pauli (a j) (b j)) - LinearMap.id) :
          Submodule ℂ ((Fin n → ZMod 2) → ℂ)) =
      2 ^ (n - r) := by
  classical
  have hsq' : ∀ j, generator a b c j * generator a b c j = 1 := hsq
  have hcomm' : ∀ j k, Commute (generator a b c j) (generator a b c k) := hcomm
  have hspace : (⨅ j, LinearMap.ker (Matrix.toLin' (c j • pauli (a j) (b j))
        - LinearMap.id) : Submodule ℂ ((Fin n → ZMod 2) → ℂ))
      = LinearMap.range (Matrix.toLin' (codeProjector a b c)) := by
    have hcs : (⨅ j, LinearMap.ker (Matrix.toLin' (c j • pauli (a j) (b j))
        - LinearMap.id) : Submodule ℂ ((Fin n → ZMod 2) → ℂ)) = codeSpace a b c := rfl
    rw [hcs, ← range_toLin'_codeProjector hsq' hcomm']
  rw [hspace]
  have hPP : codeProjector a b c * codeProjector a b c = codeProjector a b c :=
    codeProjector_mul_self hsq' hcomm'
  have hidem : IsIdempotentElem (Matrix.toLin' (codeProjector a b c)) := by
    show Matrix.toLin' (codeProjector a b c) * Matrix.toLin' (codeProjector a b c)
      = Matrix.toLin' (codeProjector a b c)
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hPP]
  have hproj := LinearMap.IsIdempotentElem.isProj_range _ hidem
  have htrace := LinearMap.IsProj.trace hproj
  have hmat : LinearMap.trace ℂ ((Fin n → ZMod 2) → ℂ)
      (Matrix.toLin' (codeProjector a b c)) = (codeProjector a b c).trace := by
    rw [LinearMap.trace_eq_matrix_trace _ (Pi.basisFun ℂ (Fin n → ZMod 2)) _,
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  have hPtrace : (codeProjector a b c).trace = (2 : ℂ) ^ (n - r) :=
    trace_codeProjector hsq' hcomm' hind
  have hce : LinearMap.trace ℂ ((Fin n → ZMod 2) → ℂ)
      (Matrix.toLin' (codeProjector a b c)) = (2 : ℂ) ^ (n - r) := by
    rw [hmat, hPtrace]
  have hcast : (2 : ℂ) ^ (n - r) = ((2 ^ (n - r) : ℕ) : ℂ) := by norm_cast
  have hfin_cast := htrace.symm.trans (hce.trans hcast)
  exact Nat.cast_injective (R := ℂ) hfin_cast

/-- The two `X^a Z^b` carriers on main agree. -/
theorem pauli_eq_pauliXZ {n : ℕ} (a b : Fin n → ZMod 2) :
    pauli a b = MathlibExt.Quantum.PauliXZ.pauliXZ a b :=
  pauli_eq_pauliXZ_aux a b

end Cslib.CodingTheory.StabilizerCode
