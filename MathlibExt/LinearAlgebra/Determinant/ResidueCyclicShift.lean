/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Determinant and coordinates of a weighted cyclic shift

Let k,l be fields with an algebra map k→l, r∈ℕ and q∈lˣ. On e=r+1 blocks, T_q sends x_r to
q⁻¹x_r at block0 and x_j to block j+1 for j<r. For a∈lˣ let P_a multiply every block by a, and
P_(a,q,m)=T_q^m∘P_a. When l is finite-dimensional over k, put d=[l:k] and N(x)=Norm_(l/k)(x).
Then det_k(T_q)=(-1)^(dr)N(q)⁻¹ and det_k(P_(a,q,m))=det_k(T_q)^m N(a)^(r+1). A vector at
block i moves to (i+m) mod e with coefficient (q⁻¹)^((i+m) div e)*a, for e=r+1.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uK uL

open Equiv

namespace LinearEquiv

variable (k : Type uK) (l : Type uL) [Field k] [Field l] [Algebra k l]

/-- **Final-block diagonal inverse weight.**

Let l be a field,r∈ℕ,q∈lˣ. The equivalence residueCyclicDiagonal on l^(r+1) multiplies only
the final coordinate by q⁻¹ and fixes the others.
-/
noncomputable def residueCyclicDiagonal (r : ℕ) (q : lˣ) :
    (Fin (r + 1) → l) ≃ₗ[l] (Fin (r + 1) → l) :=
  LinearEquiv.piCongrRight fun i ↦
    if i = Fin.last r then (q⁻¹).mulLeftLinearEquiv l l else LinearEquiv.refl l l

/-- **Forward cyclic reindexing of scalar blocks.**

Let l be a field and e=r+1. The l-linear equivalence residueCyclicReindex l r moves each
coordinate forward by one modulo e, with x′_i=x_(rotate⁻¹(i)).
-/
noncomputable def residueCyclicReindex (r : ℕ) :
    (Fin (r + 1) → l) ≃ₗ[l] (Fin (r + 1) → l) :=
  LinearEquiv.piCongrLeft l (fun _ : Fin (r + 1) ↦ l) (finRotate (r + 1))

/-- **Coordinate of cyclic reindexing.**

Let l be a field,r∈ℕ and x:Fin(r+1)→l. Then residueCyclicReindex l r x
i=x((finRotate(r+1))⁻¹(i)).
-/
@[simp]
theorem residueCyclicReindex_apply (r : ℕ) (x : Fin (r + 1) → l)
    (i : Fin (r + 1)) :
    residueCyclicReindex l r x i = x ((finRotate (r + 1)).symm i) := by
  simp [residueCyclicReindex, LinearEquiv.piCongrLeft,
    LinearEquiv.piCongrLeft']

/-- **Weighted cyclic shift over the coefficient field.**

Let l be a field,r∈ℕ and q∈lˣ. The l-linear equivalence residueCyclicShiftOver has
(T_qx)_0=q⁻¹x_r and (T_qx)_(j+1)=x_j for j<r.
-/
noncomputable def residueCyclicShiftOver (r : ℕ) (q : lˣ) :
    (Fin (r + 1) → l) ≃ₗ[l] (Fin (r + 1) → l) :=
  (residueCyclicDiagonal l r q).trans (residueCyclicReindex l r)

/-- **Weighted cyclic shift restricted to a base field.**

Let k,l be fields with an algebra map k→l, r∈ℕ and q∈lˣ. On e=r+1 blocks, T_q sends x_r to
q⁻¹x_r at block0 and x_j to block j+1 for j<r. For a∈lˣ let P_a multiply every block by a, and
P_(a,q,m)=T_q^m∘P_a. The k-linear equivalence residueCyclicShift k l r q is T_q on the r+1
blocks.
-/
noncomputable def residueCyclicShift (r : ℕ) (q : lˣ) :
    (Fin (r + 1) → l) ≃ₗ[k] (Fin (r + 1) → l) :=
  (residueCyclicShiftOver l r q).restrictScalars k

/-- **Pointwise multiplication on every scalar block.**

Let l be a field,r∈ℕ and a∈lˣ. The l-linear equivalence residuePointwiseMulOver is
P_a:x_i↦a*x_i on every block.
-/
noncomputable def residuePointwiseMulOver (r : ℕ) (a : lˣ) :
    (Fin (r + 1) → l) ≃ₗ[l] (Fin (r + 1) → l) :=
  LinearEquiv.piCongrRight fun _ ↦ a.mulLeftLinearEquiv l l

/-- **Pointwise block multiplication over the base field.**

Let k,l be fields with an algebra map k→l, r∈ℕ and q∈lˣ. On e=r+1 blocks, T_q sends x_r to
q⁻¹x_r at block0 and x_j to block j+1 for j<r. For a∈lˣ let P_a multiply every block by a, and
P_(a,q,m)=T_q^m∘P_a. The k-linear equivalence residuePointwiseMul is P_a:x_i↦a*x_i on every
block.
-/
noncomputable def residuePointwiseMul (r : ℕ) (a : lˣ) :
    (Fin (r + 1) → l) ≃ₗ[k] (Fin (r + 1) → l) :=
  (residuePointwiseMulOver l r a).restrictScalars k

/-- **Periodic multiplication followed by weighted cyclic shifts.**

Let k,l be fields with an algebra map k→l, r∈ℕ and q∈lˣ. On e=r+1 blocks, T_q sends x_r to
q⁻¹x_r at block0 and x_j to block j+1 for j<r. For a∈lˣ let P_a multiply every block by a, and
P_(a,q,m)=T_q^m∘P_a. The k-linear equivalence residuePeriodicMul r a q m is
P_(a,q,m)=T_q^m∘P_a.
-/
noncomputable def residuePeriodicMul (r : ℕ) (a q : lˣ) (m : ℕ) :
    (Fin (r + 1) → l) ≃ₗ[k] (Fin (r + 1) → l) :=
  (residuePointwiseMul k l r a).trans ((residueCyclicShift k l r q) ^ m)

/-- **Reindexing a positive block count.**

Let k→l be an extension of fields,e∈ℕ with e>0. The k-linear equivalence
residuePositiveLengthReindex identifies l^(e-1+1) with l^e by the unchanged natural coordinate
values.
-/
noncomputable def residuePositiveLengthReindex (e : ℕ) (he : 0 < e) :
    (Fin (e - 1 + 1) → l) ≃ₗ[k] (Fin e → l) :=
  LinearEquiv.piCongrLeft k (fun _ : Fin e ↦ l)
    (finCongr (Nat.sub_add_cancel he))

/-- **Positive-length periodic residue map.**

Let k→l be an extension of fields, e>0, a,q∈lˣ and m∈ℕ. On l^e put (T_q x)_0=q⁻¹x_(e-1), (T_q
x)_(j+1)=x_j and (P_a x)_i=a*x_i. Then residuePeriodicMulOfPositiveLength is T_q^m∘P_a on
exactly Fin e coordinates.
-/
noncomputable def residuePeriodicMulOfPositiveLength
    (e : ℕ) (he : 0 < e) (a q : lˣ) (m : ℕ) :
    (Fin e → l) ≃ₗ[k] (Fin e → l) :=
  (((residuePositiveLengthReindex k l e he).symm.trans
    (residuePeriodicMul k l (e - 1) a q m)).trans
      (residuePositiveLengthReindex k l e he))

/-- **Periodic target permutation.**

For e,m∈ℕ, residuePeriodicTargetEquiv e m=(finRotate e)^m as a permutation of Fin e. For e>0
it sends i to (i+m) mod e; Fin0 is empty.
-/
def residuePeriodicTargetEquiv (e m : ℕ) : Equiv.Perm (Fin e) :=
  (finRotate e) ^ m

/-- **Target of a forward periodic coordinate.**

For positive e, i∈Fin e and m∈ℕ, let target(i,m)=(i+m) mod e and crossings(i,m)=(i+m) div e.
The index residuePeriodicTarget e he i m is target(i,m).
-/
def residuePeriodicTarget (e : ℕ) (he : 0 < e) (r : Fin e) (m : ℕ) : Fin e :=
  ⟨(r.1 + m) % e, Nat.mod_lt _ he⟩

/-- **Number of cyclic wrap crossings.**

For positive e, i∈Fin e and m∈ℕ, let target(i,m)=(i+m) mod e and crossings(i,m)=(i+m) div e.
The natural number residuePeriodicCrossings e i m is crossings(i,m).
-/
def residuePeriodicCrossings (e : ℕ) (r : Fin e) (m : ℕ) : ℕ :=
  (r.1 + m) / e

/-- **Periodic permutation agrees with its modular target.**

For positive e, i∈Fin e and m∈ℕ, let target(i,m)=(i+m) mod e and crossings(i,m)=(i+m) div e.
For e>0, residuePeriodicTargetEquiv e m i=residuePeriodicTarget e he i m.
-/
@[simp]
theorem residuePeriodicTargetEquiv_apply
    (e : ℕ) (he : 0 < e) (r : Fin e) (m : ℕ) :
    residuePeriodicTargetEquiv e m r = residuePeriodicTarget e he r m := by
  induction m with
  | zero =>
      apply Fin.ext
      simp [residuePeriodicTargetEquiv, residuePeriodicTarget,
        Nat.mod_eq_of_lt r.isLt]
  | succ m ih =>
      rw [residuePeriodicTargetEquiv, pow_succ', Equiv.Perm.mul_apply]
      rw [show ((finRotate e) ^ m) r = residuePeriodicTarget e he r m from ih]
      apply Fin.ext
      simp only [finRotate_apply, Fin.add_def, Fin.val_one',
        residuePeriodicTarget, Fin.val_mk]
      calc
        (((r.1 + m) % e + 1 % e) % e) =
            (r.1 + m + 1) % e := (Nat.add_mod _ _ _).symm
        _ = (r.1 + (m + 1)) % e := by congr 1

@[simp]
theorem residuePointwiseMul_apply (r : ℕ) (a : lˣ)
    (x : Fin (r + 1) → l) (i : Fin (r + 1)) :
    residuePointwiseMul k l r a x i = (a : l) * x i :=
  rfl

/-- **Coordinate formula of a weighted cyclic shift.**

Let k,l be fields with an algebra map k→l, r∈ℕ and q∈lˣ. On e=r+1 blocks, T_q sends x_r to
q⁻¹x_r at block0 and x_j to block j+1 for j<r. For a∈lˣ let P_a multiply every block by a, and
P_(a,q,m)=T_q^m∘P_a. For x:Fin(r+1)→l and i, put j=rotate⁻¹(i). Then (T_qx)_i=q⁻¹x_j if j=r,
and x_j otherwise.
-/
@[simp]
theorem residueCyclicShift_apply (r : ℕ) (q : lˣ)
    (x : Fin (r + 1) → l) (i : Fin (r + 1)) :
    residueCyclicShift k l r q x i =
      if (finRotate (r + 1)).symm i = Fin.last r then
        (q⁻¹ : l) * x ((finRotate (r + 1)).symm i)
      else x ((finRotate (r + 1)).symm i) := by
  rw [residueCyclicShift, LinearEquiv.restrictScalars_apply,
    residueCyclicShiftOver, LinearEquiv.trans_apply,
    residueCyclicReindex_apply, residueCyclicDiagonal,
    LinearEquiv.piCongrRight_apply]
  split_ifs
  · simp only [Units.mulLeftLinearEquiv_apply, Units.val_inv_eq_inv_val]
  · rfl

/-- **Final coordinate wraps to zero with inverse weight.**

Let k,l be fields with an algebra map k→l, r∈ℕ and q∈lˣ. On e=r+1 blocks, T_q sends x_r to
q⁻¹x_r at block0 and x_j to block j+1 for j<r. For a∈lˣ let P_a multiply every block by a, and
P_(a,q,m)=T_q^m∘P_a. For x:Fin(r+1)→l, (T_qx)_0=q⁻¹x_r.
-/
@[simp, nolint simpNF]
theorem residueCyclicShift_apply_zero (r : ℕ) (q : lˣ)
    (x : Fin (r + 1) → l) :
    residueCyclicShift k l r q x 0 = (q⁻¹ : l) * x (Fin.last r) := by
  rw [residueCyclicShift_apply]
  have hlast : (-1 : Fin (r + 1)) = Fin.last r := by
    calc
      (-1 : Fin (r + 1)) = -(-Fin.last r) := by rw [Fin.neg_last]
      _ = Fin.last r := neg_neg _
  have hzero : (0 : Fin (r + 1)) - 1 = Fin.last r := by
    rw [zero_sub, hlast]
  rw [finRotate_symm_apply, hzero]
  simp

/-- **A nonfinal coordinate advances unweighted.**

Let k,l be fields with an algebra map k→l, r∈ℕ and q∈lˣ. On e=r+1 blocks, T_q sends x_r to
q⁻¹x_r at block0 and x_j to block j+1 for j<r. For a∈lˣ let P_a multiply every block by a, and
P_(a,q,m)=T_q^m∘P_a. For j<r, (T_qx)_(j+1)=x_j.
-/
@[simp, nolint simpNF]
theorem residueCyclicShift_apply_succ (r : ℕ) (q : lˣ)
    (x : Fin (r + 1) → l) (i : Fin r) :
    residueCyclicShift k l r q x i.succ = x i.castSucc := by
  rw [residueCyclicShift_apply]
  have hpred : i.succ - 1 = i.castSucc := by
    apply Fin.ext
    rw [Fin.val_sub_one_of_ne_zero (Fin.succ_ne_zero i)]
    simp
  rw [finRotate_symm_apply, hpred]
  simp

/-- **Single-coordinate value of one weighted shift.**

Let k,l be fields with an algebra map k→l, r∈ℕ and q∈lˣ. On e=r+1 blocks, T_q sends x_r to
q⁻¹x_r at block0 and x_j to block j+1 for j<r. For a∈lˣ let P_a multiply every block by a, and
P_(a,q,m)=T_q^m∘P_a. For i∈Fin(r+1), T_q(δ_i x)=δ_(rotate i)((if i=r then q⁻¹ else1)*x), where
δ_i is a one-coordinate vector.
-/
theorem residueCyclicShift_apply_single (r : ℕ) (q : lˣ)
    (i : Fin (r + 1)) (x : l) :
    residueCyclicShift k l r q (Pi.single i x) =
      Pi.single (finRotate (r + 1) i)
        (if i = Fin.last r then (q⁻¹ : l) * x else x) := by
  classical
  ext j
  rw [residueCyclicShift_apply]
  by_cases hji : (finRotate (r + 1)).symm j = i
  · have hj : j = finRotate (r + 1) i := by
      simpa using congrArg (finRotate (r + 1)) hji
    subst j
    simp
  · have hj : j ≠ finRotate (r + 1) i := by
      intro h
      apply hji
      rw [h]
      exact (finRotate (r + 1)).symm_apply_apply i
    have hsingle :
        Pi.single (M := fun _ : Fin (r + 1) => l) i x
          ((finRotate (r + 1)).symm j) = 0 := by
      rw [Pi.single_eq_of_ne hji]
    simp only [hsingle, mul_zero, ite_self]
    rw [Pi.single_eq_of_ne hj]

/-- **Single-coordinate value after multiple weighted shifts.**

Let k,l be fields with an algebra map k→l, r∈ℕ and q∈lˣ. On e=r+1 blocks, T_q sends x_r to
q⁻¹x_r at block0 and x_j to block j+1 for j<r. For a∈lˣ let P_a multiply every block by a, and
P_(a,q,m)=T_q^m∘P_a. For e=r+1 and i∈Fin e, T_q^m(δ_i x)=δ_((i+m) mod e)((q⁻¹)^((i+m) div
e)*x).
-/
theorem residueCyclicShift_pow_apply_single (r : ℕ) (q : lˣ) (m : ℕ)
    (i : Fin (r + 1)) (x : l) :
    ((residueCyclicShift k l r q) ^ m)
        (Pi.single (M := fun _ : Fin (r + 1) => l) i x) =
      Pi.single (M := fun _ : Fin (r + 1) => l)
        (residuePeriodicTarget (r + 1) (Nat.succ_pos r) i m)
        ((q⁻¹ : l) ^ residuePeriodicCrossings (r + 1) i m * x) := by
  classical
  induction m with
  | zero =>
      have ht : residuePeriodicTarget (r + 1) (Nat.succ_pos r) i 0 = i := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt i.isLt
      have hc : residuePeriodicCrossings (r + 1) i 0 = 0 := by
        exact Nat.div_eq_of_lt i.isLt
      simp [ht, hc]
  | succ m ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih,
        residueCyclicShift_apply_single]
      let s := residuePeriodicTarget (r + 1) (Nat.succ_pos r) i m
      let c := residuePeriodicCrossings (r + 1) i m
      have htarget : finRotate (r + 1) s =
          residuePeriodicTarget (r + 1) (Nat.succ_pos r) i (m + 1) := by
        apply Fin.ext
        simp only [s, residuePeriodicTarget, Fin.val_mk, finRotate_apply,
          Fin.add_def, Fin.val_one']
        calc
          ((i.1 + m) % (r + 1) + 1 % (r + 1)) % (r + 1) =
              (i.1 + m + 1) % (r + 1) := (Nat.add_mod _ _ _).symm
          _ = (i.1 + (m + 1)) % (r + 1) := by
            congr 1
      rw [htarget]
      by_cases hs : s = Fin.last r
      · have hcross : residuePeriodicCrossings (r + 1) i (m + 1) = c + 1 := by
          have hm := Nat.mod_add_div (i.1 + m) (r + 1)
          have hm1 := Nat.mod_add_div (i.1 + (m + 1)) (r + 1)
          have hsval := congrArg Fin.val hs
          change (i.1 + m) % (r + 1) = r at hsval
          have hmod1 : (i.1 + (m + 1)) % (r + 1) = 0 := by
            calc
              (i.1 + (m + 1)) % (r + 1) =
                  (i.1 + m + 1) % (r + 1) := by
                    congr 1
              _ = (((i.1 + m) % (r + 1)) + 1) % (r + 1) :=
                (Nat.mod_add_mod _ _ _).symm
              _ = 0 := by rw [hsval, Nat.add_one, Nat.mod_self]
          change (i.1 + (m + 1)) / (r + 1) =
            (i.1 + m) / (r + 1) + 1
          rw [hsval] at hm
          rw [hmod1] at hm1
          apply Nat.mul_left_cancel (Nat.succ_pos r)
          calc
            (r + 1) * ((i.1 + (m + 1)) / (r + 1)) = i.1 + (m + 1) := by
              omega
            _ = i.1 + m + 1 := by omega
            _ = r + (r + 1) * ((i.1 + m) / (r + 1)) + 1 := by
              omega
            _ = (r + 1) * ((i.1 + m) / (r + 1) + 1) := by
              ring
        have hs' : residuePeriodicTarget (r + 1) (Nat.succ_pos r) i m =
            Fin.last r := hs
        rw [ite_eq_left hs', hcross, pow_succ]
        congr 1
        ring
      · have hcross : residuePeriodicCrossings (r + 1) i (m + 1) = c := by
          have hm := Nat.mod_add_div (i.1 + m) (r + 1)
          have hm1 := Nat.mod_add_div (i.1 + (m + 1)) (r + 1)
          have hsval : (i.1 + m) % (r + 1) ≠ r := by
            intro h
            apply hs
            apply Fin.ext
            exact h
          have hslt := Nat.mod_lt (i.1 + m) (Nat.succ_pos r)
          have hmod1 : (i.1 + (m + 1)) % (r + 1) =
              (i.1 + m) % (r + 1) + 1 := by
            calc
              (i.1 + (m + 1)) % (r + 1) =
                  (i.1 + m + 1) % (r + 1) := by
                    congr 1
              _ = (((i.1 + m) % (r + 1)) + 1) % (r + 1) :=
                (Nat.mod_add_mod _ _ _).symm
              _ = (i.1 + m) % (r + 1) + 1 :=
                Nat.mod_eq_of_lt (by
                  have hsle : (i.1 + m) % (r + 1) ≤ r :=
                    Nat.lt_succ_iff.mp hslt
                  have hslt' : (i.1 + m) % (r + 1) < r :=
                    lt_of_le_of_ne hsle hsval
                  simpa only [Nat.add_one] using Nat.succ_lt_succ hslt')
          change (i.1 + (m + 1)) / (r + 1) = (i.1 + m) / (r + 1)
          rw [hmod1] at hm1
          have hadd :
              (i.1 + m) % (r + 1) + 1 +
                  (r + 1) * ((i.1 + (m + 1)) / (r + 1)) =
                (i.1 + m) % (r + 1) + 1 +
                  (r + 1) * ((i.1 + m) / (r + 1)) := by
            calc
              _ = i.1 + (m + 1) := hm1
              _ = i.1 + m + 1 := by omega
              _ = ((i.1 + m) % (r + 1) +
                    (r + 1) * ((i.1 + m) / (r + 1))) + 1 := by
                      rw [hm]
              _ = _ := by omega
          have hmul :
              (r + 1) * ((i.1 + (m + 1)) / (r + 1)) =
                (r + 1) * ((i.1 + m) / (r + 1)) :=
            Nat.add_left_cancel hadd
          exact Nat.mul_left_cancel (Nat.succ_pos r) hmul
        have hs' : residuePeriodicTarget (r + 1) (Nat.succ_pos r) i m ≠
            Fin.last r := hs
        rw [ite_eq_right hs', hcross]

/-- **Single-coordinate value of periodic multiplication.**

Let k,l be fields with an algebra map k→l, r∈ℕ and q∈lˣ. On e=r+1 blocks, T_q sends x_r to
q⁻¹x_r at block0 and x_j to block j+1 for j<r. For a∈lˣ let P_a multiply every block by a, and
P_(a,q,m)=T_q^m∘P_a. For e=r+1, P_(a,q,m)(δ_i x)=δ_((i+m) mod e)((q⁻¹)^((i+m) div e)*(a*x)).
-/
theorem residuePeriodicMul_apply_single (r : ℕ) (a q : lˣ) (m : ℕ)
    (i : Fin (r + 1)) (x : l) :
    residuePeriodicMul k l r a q m
        (Pi.single (M := fun _ : Fin (r + 1) ↦ l) i x) =
      Pi.single (M := fun _ : Fin (r + 1) ↦ l)
        (residuePeriodicTarget (r + 1) (Nat.succ_pos r) i m)
        ((q⁻¹ : l) ^ residuePeriodicCrossings (r + 1) i m * ((a : l) * x)) := by
  classical
  rw [residuePeriodicMul, LinearEquiv.trans_apply]
  have hpointwise :
      residuePointwiseMul k l r a
          (Pi.single (M := fun _ : Fin (r + 1) ↦ l) i x) =
        Pi.single (M := fun _ : Fin (r + 1) ↦ l) i ((a : l) * x) := by
    ext j
    simp only [residuePointwiseMul_apply]
    by_cases hji : j = i
    · subst j
      simp
    · rw [Pi.single_eq_of_ne hji, Pi.single_eq_of_ne hji, mul_zero]
  rw [hpointwise, residueCyclicShift_pow_apply_single]

/-- **Positive-length periodic map on a single coordinate.**

Let k→l be an extension of fields, e>0, a,q∈lˣ,m∈ℕ and i∈Fin e. Then
residuePeriodicMulOfPositiveLength(δ_i x)=δ_((i+m) mod e)((q⁻¹)^((i+m) div e)*(a*x)).
-/
theorem residuePeriodicMulOfPositiveLength_apply_single
    (e : ℕ) (he : 0 < e) (a q : lˣ) (m : ℕ) (i : Fin e) (x : l) :
    residuePeriodicMulOfPositiveLength k l e he a q m
        (Pi.single (M := fun _ : Fin e ↦ l) i x) =
      Pi.single (M := fun _ : Fin e ↦ l)
        (residuePeriodicTarget e he i m)
        ((q⁻¹ : l) ^ residuePeriodicCrossings e i m * ((a : l) * x)) := by
  classical
  let hlen : e - 1 + 1 = e := Nat.sub_add_cancel he
  let i' : Fin (e - 1 + 1) := i.cast hlen.symm
  have hreindex_symm :
      (residuePositiveLengthReindex k l e he).symm
          (Pi.single (M := fun _ : Fin e ↦ l) i x) =
        Pi.single (M := fun _ : Fin (e - 1 + 1) ↦ l) i' x := by
    ext j
    change
      Pi.single (M := fun _ : Fin e ↦ l) i x (finCongr hlen j) =
        Pi.single (M := fun _ : Fin (e - 1 + 1) ↦ l) i' x j
    have hindex : finCongr hlen j = i ↔ j = i' := by
      constructor
      · intro h
        apply Fin.ext
        simpa [i'] using congrArg Fin.val h
      · intro h
        subst j
        rfl
    simp only [Pi.single_apply]
    rw [if_congr hindex rfl rfl]
  rw [residuePeriodicMulOfPositiveLength, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, hreindex_symm,
    residuePeriodicMul_apply_single]
  ext j
  change
    Pi.single (M := fun _ : Fin (e - 1 + 1) ↦ l)
        (residuePeriodicTarget (e - 1 + 1) (Nat.succ_pos (e - 1)) i' m)
        ((q⁻¹ : l) ^ residuePeriodicCrossings (e - 1 + 1) i' m * ((a : l) * x))
        ((finCongr hlen).symm j) =
      Pi.single (M := fun _ : Fin e ↦ l) (residuePeriodicTarget e he i m)
        ((q⁻¹ : l) ^ residuePeriodicCrossings e i m * ((a : l) * x)) j
  have htarget :
      finCongr hlen
          (residuePeriodicTarget (e - 1 + 1) (Nat.succ_pos (e - 1)) i' m) =
        residuePeriodicTarget e he i m := by
    apply Fin.ext
    simp [residuePeriodicTarget, i', hlen]
  have hcross :
      residuePeriodicCrossings (e - 1 + 1) i' m =
        residuePeriodicCrossings e i m := by
    simp [residuePeriodicCrossings, i', hlen]
  rw [hcross]
  simp only [Pi.single_apply]
  have hindex :
      (finCongr hlen).symm j =
          residuePeriodicTarget (e - 1 + 1) (Nat.succ_pos (e - 1)) i' m ↔
        j = residuePeriodicTarget e he i m := by
    rw [← htarget]
    exact (finCongr hlen).symm_apply_eq
  rw [if_congr hindex rfl rfl]

/-- **Inverse periodic map on a single target coordinate.**

Let k→l be an extension of fields, e>0, a,q∈lˣ,m∈ℕ and target s∈Fin e. Let S send δ_i x to
δ_((i+m) mod e)((q⁻¹)^((i+m) div e)*a*x). For i the inverse image of s under the target
permutation and c=(i+m) div e, S⁻¹ sends δ_s x to δ_i((((q⁻¹)^c*a)⁻¹)*x).
-/
theorem residuePeriodicMulOfPositiveLength_symm_apply_single
    (e : ℕ) (he : 0 < e) (a q : lˣ) (m : ℕ) (s : Fin e) (x : l) :
    let r := (residuePeriodicTargetEquiv e m).symm s
    let c := residuePeriodicCrossings e r m
    (residuePeriodicMulOfPositiveLength k l e he a q m).symm
        (Pi.single (M := fun _ : Fin e ↦ l) s x) =
      Pi.single (M := fun _ : Fin e ↦ l) r
        ((((((q⁻¹) ^ c) * a)⁻¹ : lˣ) : l) * x) := by
  dsimp only
  let r := (residuePeriodicTargetEquiv e m).symm s
  let c := residuePeriodicCrossings e r m
  change (residuePeriodicMulOfPositiveLength k l e he a q m).symm
      (Pi.single (M := fun _ : Fin e ↦ l) s x) =
    Pi.single (M := fun _ : Fin e ↦ l) r
      ((((((q⁻¹) ^ c) * a)⁻¹ : lˣ) : l) * x)
  apply (residuePeriodicMulOfPositiveLength k l e he a q m).injective
  rw [LinearEquiv.apply_symm_apply,
    residuePeriodicMulOfPositiveLength_apply_single]
  have hrs : residuePeriodicTarget e he r m = s := by
    rw [← residuePeriodicTargetEquiv_apply]
    exact (residuePeriodicTargetEquiv e m).apply_symm_apply s
  rw [hrs]
  congr 1
  let u : lˣ := (q⁻¹) ^ c * a
  change x = (q⁻¹ : l) ^ c * ((a : l) * (((u⁻¹ : lˣ) : l) * x))
  rw [← mul_assoc]
  have hu : (u : l) = (q⁻¹ : l) ^ c * (a : l) := by simp [u]
  rw [← hu]
  simp

/-- **Determinant of the final-block inverse weight.**

Let l be a field,r∈ℕ,q∈lˣ. Over l, det(residueCyclicDiagonal l r q)=q⁻¹.
-/
theorem det_residueCyclicDiagonal (r : ℕ) (q : lˣ) :
    LinearMap.det
        (residueCyclicDiagonal l r q :
          (Fin (r + 1) → l) →ₗ[l] (Fin (r + 1) → l)) =
      (q⁻¹ : l) := by
  have hmap :
      (residueCyclicDiagonal l r q :
          (Fin (r + 1) → l) →ₗ[l] (Fin (r + 1) → l)) =
        LinearMap.pi (fun i ↦
          ((if i = Fin.last r then (q⁻¹).mulLeftLinearEquiv l l
              else LinearEquiv.refl l l) :
            l →ₗ[l] l).comp (LinearMap.proj i)) := by
    apply LinearMap.ext
    intro x
    funext i
    simp [residueCyclicDiagonal]
    split <;> rfl
  rw [hmap, LinearMap.det_pi]
  classical
  calc
    ∏ i : Fin (r + 1), LinearMap.det
        ((if i = Fin.last r then (q⁻¹).mulLeftLinearEquiv l l
            else LinearEquiv.refl l l) :
          l →ₗ[l] l) =
        ∏ i : Fin (r + 1), if i = Fin.last r then (q⁻¹ : l) else 1 := by
          apply Finset.prod_congr rfl
          intro i _
          split_ifs
          · rw [Units.toLinearMap_mulLeftLinearEquiv, LinearMap.det_mulLeft]
            exact Units.val_inv_eq_inv_val q
          · exact LinearMap.det_id
    _ = (q⁻¹ : l) := by
      exact Fintype.prod_ite_eq' (Fin.last r)
        (fun _ : Fin (r + 1) ↦ (q⁻¹ : l))

/-- **Determinant of a forward cyclic block permutation.**

Let l be a field and r∈ℕ. Over l, det(residueCyclicReindex l r)=(-1)^r.
-/
theorem det_residueCyclicReindex (r : ℕ) :
    LinearMap.det
        (residueCyclicReindex l r :
          (Fin (r + 1) → l) →ₗ[l] (Fin (r + 1) → l)) =
      (-1 : l) ^ r := by
  let b := Pi.basisFun l (Fin (r + 1))
  rw [← LinearMap.det_toMatrix b]
  have hmat :
      LinearMap.toMatrix b b
          (residueCyclicReindex l r :
            (Fin (r + 1) → l) →ₗ[l] (Fin (r + 1) → l)) =
        ((finRotate (r + 1))⁻¹).permMatrix l := by
    ext i j
    simp only [LinearMap.toMatrix_apply', b, Pi.basisFun_repr,
      residueCyclicReindex, LinearEquiv.coe_coe, LinearEquiv.piCongrLeft]
    classical
    by_cases h : i - 1 = j <;> simp [h]
  rw [hmat, Matrix.det_permutation, Equiv.Perm.sign_inv]
  have hs : Perm.sign (finRotate (r + 1)) = (-1 : ℤˣ) ^ r := by
    rw [sign_finRotate, add_tsub_cancel_right]
  calc
    ((Perm.sign (finRotate (r + 1)) : ℤˣ) : l) =
        (((-1 : ℤˣ) ^ r : ℤˣ) : l) := congrArg (fun z : ℤˣ ↦ (z : l)) hs
    _ = (-1 : l) ^ r := by simp

/-- **Coefficient-field determinant of the weighted shift.**

Let l be a field,r∈ℕ,q∈lˣ. Over l, det(residueCyclicShiftOver l r q)=(-1)^r*q⁻¹.
-/
theorem det_residueCyclicShiftOver (r : ℕ) (q : lˣ) :
    LinearMap.det
        (residueCyclicShiftOver l r q :
          (Fin (r + 1) → l) →ₗ[l] (Fin (r + 1) → l)) =
      (-1 : l) ^ r * (q⁻¹ : l) := by
  rw [show (residueCyclicShiftOver l r q :
      (Fin (r + 1) → l) →ₗ[l] (Fin (r + 1) → l)) =
      (residueCyclicReindex l r :
        (Fin (r + 1) → l) →ₗ[l] (Fin (r + 1) → l)).comp
          (residueCyclicDiagonal l r q :
            (Fin (r + 1) → l) →ₗ[l] (Fin (r + 1) → l)) by rfl]
  rw [LinearMap.det_comp, det_residueCyclicReindex,
    det_residueCyclicDiagonal]

/-- **Coefficient-field determinant of pointwise block multiplication.**

Let l be a field,r∈ℕ,a∈lˣ. Over l, det(P_a on l^(r+1))=a^(r+1).
-/
theorem det_residuePointwiseMulOver (r : ℕ) (a : lˣ) :
    LinearMap.det
        (residuePointwiseMulOver l r a :
          (Fin (r + 1) → l) →ₗ[l] (Fin (r + 1) → l)) =
      (a : l) ^ (r + 1) := by
  have hmap :
      (residuePointwiseMulOver l r a :
          (Fin (r + 1) → l) →ₗ[l] (Fin (r + 1) → l)) =
        LinearMap.pi (fun i ↦
          (a.mulLeftLinearEquiv l l : l →ₗ[l] l).comp
            (LinearMap.proj i)) := by
    apply LinearMap.ext
    intro x
    funext i
    rfl
  rw [hmap, LinearMap.det_pi]
  simp only [Units.toLinearMap_mulLeftLinearEquiv, LinearMap.det_mulLeft,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Base-field determinant of pointwise block multiplication.**

Let k,l be fields with an algebra map k→l, r∈ℕ and q∈lˣ. On e=r+1 blocks, T_q sends x_r to
q⁻¹x_r at block0 and x_j to block j+1 for j<r. For a∈lˣ let P_a multiply every block by a, and
P_(a,q,m)=T_q^m∘P_a. The algebra determinant satisfies det_k(P_a)=Algebra.norm k a^(r+1). For
an infinite-dimensional field extension, this API uses the generalized determinant and
algebra-norm value1 convention.
-/
theorem det_residuePointwiseMul
    (r : ℕ) (a : lˣ) :
    (LinearEquiv.det (residuePointwiseMul k l r a) : k) =
      Algebra.norm k (a : l) ^ (r + 1) := by
  rw [LinearEquiv.coe_det]
  change LinearMap.det
      ((residuePointwiseMulOver l r a :
        (Fin (r + 1) → l) →ₗ[l] (Fin (r + 1) → l)).restrictScalars k) = _
  rw [LinearMap.det_restrictScalars, det_residuePointwiseMulOver, map_pow]

/-- **Base-field determinant of the weighted cyclic shift.**

Let k,l be fields with an algebra map k→l, r∈ℕ and q∈lˣ. On e=r+1 blocks, T_q sends x_r to
q⁻¹x_r at block0 and x_j to block j+1 for j<r. For a∈lˣ let P_a multiply every block by a, and
P_(a,q,m)=T_q^m∘P_a. When l is finite-dimensional over k, put d=[l:k] and N(x)=Norm_(l/k)(x).
The determinant is det_k(T_q)=(-1)^(d*r)*N(q)⁻¹.
-/
theorem det_residueCyclicShift [FiniteDimensional k l] (r : ℕ) (q : lˣ) :
    (LinearEquiv.det (residueCyclicShift k l r q) : k) =
      (-1 : k) ^ (Module.finrank k l * r) *
        (Algebra.norm k (q : l))⁻¹ := by
  rw [LinearEquiv.coe_det]
  change LinearMap.det
      ((residueCyclicShiftOver l r q :
        (Fin (r + 1) → l) →ₗ[l] (Fin (r + 1) → l)).restrictScalars k) = _
  rw [LinearMap.det_restrictScalars, det_residueCyclicShiftOver, map_mul,
    map_pow, Algebra.norm_inv]
  rw [show Algebra.norm k (-1 : l) = (-1 : k) ^ Module.finrank k l by
    simpa using (Algebra.norm_algebraMap (S := l) (-1 : k))]
  rw [← pow_mul]

/-- **Determinant of periodic weighted residue multiplication.**

Let k,l be fields with an algebra map k→l, r∈ℕ and q∈lˣ. On e=r+1 blocks, T_q sends x_r to
q⁻¹x_r at block0 and x_j to block j+1 for j<r. For a∈lˣ let P_a multiply every block by a, and
P_(a,q,m)=T_q^m∘P_a. When l is finite-dimensional over k, put d=[l:k] and N(x)=Norm_(l/k)(x).
The determinant is det_k(P_(a,q,m))=[(-1)^(d*r)*N(q)⁻¹]^m*N(a)^(r+1).
-/
theorem det_residuePeriodicMul [FiniteDimensional k l]
    (r : ℕ) (a q : lˣ) (m : ℕ) :
    (LinearEquiv.det (residuePeriodicMul k l r a q m) : k) =
      (((-1 : k) ^ (Module.finrank k l * r) *
          (Algebra.norm k (q : l))⁻¹) ^ m) *
        Algebra.norm k (a : l) ^ (r + 1) := by
  rw [residuePeriodicMul, LinearEquiv.det_trans, map_pow]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  rw [det_residueCyclicShift, det_residuePointwiseMul]

/-- **Determinant of the positive-length periodic map.**

Let l/k be a finite field extension of degree d, e>0, a,q∈lˣ and m∈ℕ. For N(x)=Norm_(l/k)(x),
the map S=T_q^m∘P_a, where T_q shifts forward with wrap weight q⁻¹ and P_a multiplies each
block by a, has determinant over k [(-1)^(d*(e-1))*N(q)⁻¹]^m*N(a)^e.
-/
theorem det_residuePeriodicMulOfPositiveLength [FiniteDimensional k l]
    (e : ℕ) (he : 0 < e) (a q : lˣ) (m : ℕ) :
    (LinearEquiv.det
        (residuePeriodicMulOfPositiveLength k l e he a q m) : k) =
      (((-1 : k) ^ (Module.finrank k l * (e - 1)) *
          (Algebra.norm k (q : l))⁻¹) ^ m) *
        Algebra.norm k (a : l) ^ e := by
  let t := residuePositiveLengthReindex k l e he
  change (LinearEquiv.det
      ((t.symm.trans (residuePeriodicMul k l (e - 1) a q m)).trans t) : k) = _
  rw [LinearEquiv.det_conj]
  rw [det_residuePeriodicMul]
  rw [Nat.sub_add_cancel he]

end LinearEquiv
