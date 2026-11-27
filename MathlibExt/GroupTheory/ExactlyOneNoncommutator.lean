/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

/-!
# A finite group with exactly one noncommutator

Hatem and Siniora, *A group with exactly one noncommutator*, arXiv:2511.00541v2,
Section 3, give the two matrices and the exceptional column for `PG368640.31`.
We check their action on the right-generator edges of `A₆` and use equation (1)
to read the commutator image of each pair as a product of two binary spans.

For coverage, seven quotient representatives suffice. The witness words below
select images whose union in the identity fiber omits just the stated column;
the other representatives have full fibers. Exclusion checks each centralizer
separately so it does not depend on having selected all commuting pairs as witnesses.
All finite checks are reductions in the Lean kernel.
-/

namespace ProductCertificate


/-- The two five-dimensional blocks are stored by columns, least-significant bit first. -/
private abbrev Bits := BitVec 5
private abbrev Block := Fin 5 → Bits
private abbrev Mat := Block × Block

private def sigmaM : Mat := (![5, 25, 15, 27, 31], ![4, 3, 12, 21, 1])
private def etaM : Mat := (![10, 7, 8, 12, 23], ![1, 5, 8, 3, 16])
private def idB : Block := ![1, 2, 4, 8, 16]
private def idM : Mat := (idB, idB)

private def pick (b : Bool) (x : Bits) : Bits := if b then x else 0

private def actB (m : Block) (x : Bits) : Bits :=
  pick (x.getLsbD 0) (m 0) ^^^ pick (x.getLsbD 1) (m 1) ^^^
  pick (x.getLsbD 2) (m 2) ^^^ pick (x.getLsbD 3) (m 3) ^^^ pick (x.getLsbD 4) (m 4)

private theorem pick_xor (a b : Bool) (x : Bits) :
    pick (a ^^ b) x = pick a x ^^^ pick b x := by cases a <;> cases b <;> simp [pick]

private theorem bit_pick (b : Bool) (x : Bits) (i : Nat) :
    (pick b x).getLsbD i = (b && x.getLsbD i) := by cases b <;> simp [pick]

private theorem actB_xor (m : Block) (x y : Bits) :
    actB m (x ^^^ y) = actB m x ^^^ actB m y := by
  simp only [actB, BitVec.getLsbD_xor, pick_xor]
  ac_rfl

private theorem actB_zero (m : Block) : actB m 0 = 0 := by simp [actB, pick]

private theorem actB_pick (m : Block) (b : Bool) (x : Bits) :
    actB m (pick b x) = pick b (actB m x) := by
  cases b
  · exact actB_zero m
  · rfl

private theorem actB_id (x : Bits) : actB idB x = x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  change (actB idB x).getLsbD i = x.getLsbD i
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;>
    simp only [actB, BitVec.getLsbD_xor, bit_pick] <;>
    simp [idB]

private theorem actB_single (m : Block) (i : Fin 5) : actB m (idB i) = m i := by
  fin_cases i <;> simp [actB, idB, pick]

private def mulM (a b : Mat) : Mat := (fun i ↦ actB a.1 (b.1 i), fun i ↦ actB a.2 (b.2 i))

private theorem actB_comp (a b : Block) (x : Bits) :
    actB (fun i ↦ actB a (b i)) x = actB a (actB b x) := by
  change _ = actB a
    (pick (x.getLsbD 0) (b 0) ^^^ pick (x.getLsbD 1) (b 1) ^^^ pick (x.getLsbD 2) (b 2) ^^^
     pick (x.getLsbD 3) (b 3) ^^^ pick (x.getLsbD 4) (b 4))
  simp only [actB_xor, actB_pick]
  rfl

private theorem mulM_assoc (a b c : Mat) : mulM (mulM a b) c = mulM a (mulM b c) :=
  Prod.ext (funext fun i ↦ actB_comp a.1 b.1 (c.1 i)) (funext fun i ↦ actB_comp a.2 b.2 (c.2 i))

private theorem mulM_id (a : Mat) : mulM a idM = a :=
  Prod.ext (funext fun i ↦ actB_single a.1 i) (funext fun i ↦ actB_single a.2 i)

private abbrev H := alternatingGroup (Fin 6)

private def sigmaSwaps : H := ⟨Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1, by
  simp [H, Equiv.Perm.sign_mul,
    show (0 : Fin 6) ≠ 4 by decide, show (0 : Fin 6) ≠ 3 by decide,
    show (0 : Fin 6) ≠ 2 by decide, show (0 : Fin 6) ≠ 1 by decide]⟩

private def etaSwaps : H := ⟨Equiv.swap 3 5 * Equiv.swap 3 4, by
  simp [H, Equiv.Perm.sign_mul,
    show (3 : Fin 6) ≠ 5 by decide, show (3 : Fin 6) ≠ 4 by decide]⟩

private def sigmaPerm : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 3, 4, 0, 5]
  invFun := ![4, 0, 1, 2, 3, 5]
  left_inv := by decide
  right_inv := by decide

private theorem sigmaPerm_eq : sigmaPerm = sigmaSwaps.val := by
  apply Equiv.ext
  decide

private def sigma : H := ⟨sigmaPerm, sigmaPerm_eq.symm ▸ sigmaSwaps.property⟩

private def etaPerm : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 5, 3]
  invFun := ![0, 1, 2, 5, 3, 4]
  left_inv := by decide
  right_inv := by decide

private theorem etaPerm_eq : etaPerm = etaSwaps.val := by
  apply Equiv.ext
  decide

private def eta : H := ⟨etaPerm, etaPerm_eq.symm ▸ etaSwaps.property⟩

private def genH (c : Bool) : H := if c then eta else sigma
private def genM (c : Bool) : Mat := if c then etaM else sigmaM

private abbrev P := Equiv.Perm (Fin 6)
private def wp (w : List Bool) : H := w.foldl (fun a c ↦ a * genH c) 1

/- The four transversals send point `n - 1` to the row index and fix points ≥ `n`.
We store the forward/inverse images and the two matrix blocks for these 18 rows
so kernel reduction does not repeatedly expand the corresponding generator words.
The word equalities, row checks, and right-generator edges below certify the data. -/
private def pw6 (i : Fin 6) : List Bool :=
  (![
    [false, true, true],
    [false, false, true, true],
    [false, false, false, true, true],
    [true],
    [true, true],
    []]) i

private def fw6 (i : Fin 6) : Fin 6 → Fin 6 :=
  (![
    ![1, 2, 3, 5, 4, 0],
    ![2, 3, 4, 5, 0, 1],
    ![3, 4, 0, 5, 1, 2],
    ![0, 1, 2, 4, 5, 3],
    ![0, 1, 2, 5, 3, 4],
    ![0, 1, 2, 3, 4, 5]]) i

private def bw6 (i : Fin 6) : Fin 6 → Fin 6 :=
  (![
    ![5, 0, 1, 2, 4, 3],
    ![4, 5, 0, 1, 2, 3],
    ![2, 4, 5, 0, 1, 3],
    ![0, 1, 2, 5, 3, 4],
    ![0, 1, 2, 4, 5, 3],
    ![0, 1, 2, 3, 4, 5]]) i

private theorem inv6 : ∀ (i : Fin 6) (j : Fin 6),
    bw6 i (fw6 i j) = j ∧ fw6 i (bw6 i j) = j := by decide +kernel

private def pk6 (i : Fin 6) : P :=
  ⟨fw6 i, bw6 i, fun j ↦ (inv6 i j).1, fun j ↦ (inv6 i j).2⟩

private theorem pk_word6 (i : Fin 6) : pk6 i = (wp (pw6 i)).val := by
  apply Equiv.ext
  revert i
  decide +kernel

private def tr6 (i : Fin 6) : H :=
  ⟨pk6 i, (pk_word6 i).symm ▸ (wp (pw6 i)).property⟩

private def mb6 (i : Fin 6) : Mat :=
  (![(![7, 10, 20, 15, 6], ![4, 17, 7, 12, 1]),
    (![19, 2, 16, 8, 22], ![12, 5, 11, 25, 4]),
    (![3, 25, 31, 27, 9], ![25, 8, 18, 16, 12]),
    (![10, 7, 8, 12, 23], ![1, 5, 8, 3, 16]),
    (![11, 5, 12, 4, 18], ![1, 9, 3, 4, 16]),
    (![1, 2, 4, 8, 16], ![1, 2, 4, 8, 16])]) i

private def pw5 (i : Fin 5) : List Bool :=
  (![
    [false],
    [false, false],
    [false, false, false],
    [true, false, true],
    []]) i

private def fw5 (i : Fin 5) : Fin 6 → Fin 6 :=
  (![
    ![1, 2, 3, 4, 0, 5],
    ![2, 3, 4, 0, 1, 5],
    ![3, 4, 0, 1, 2, 5],
    ![1, 2, 4, 0, 3, 5],
    ![0, 1, 2, 3, 4, 5]]) i

private def bw5 (i : Fin 5) : Fin 6 → Fin 6 :=
  (![
    ![4, 0, 1, 2, 3, 5],
    ![3, 4, 0, 1, 2, 5],
    ![2, 3, 4, 0, 1, 5],
    ![3, 0, 1, 4, 2, 5],
    ![0, 1, 2, 3, 4, 5]]) i

private theorem inv5 : ∀ (i : Fin 5) (j : Fin 6),
    bw5 i (fw5 i j) = j ∧ fw5 i (bw5 i j) = j := by decide +kernel

private def pk5 (i : Fin 5) : P :=
  ⟨fw5 i, bw5 i, fun j ↦ (inv5 i j).1, fun j ↦ (inv5 i j).2⟩

private theorem pk_word5 (i : Fin 5) : pk5 i = (wp (pw5 i)).val := by
  apply Equiv.ext
  revert i
  decide +kernel

private def tr5 (i : Fin 5) : H :=
  ⟨pk5 i, (pk_word5 i).symm ▸ (wp (pw5 i)).property⟩

private def mb5 (i : Fin 5) : Mat :=
  (![(![5, 25, 15, 27, 31], ![4, 3, 12, 21, 1]),
    (![10, 1, 8, 24, 23], ![12, 7, 25, 9, 4]),
    (![2, 5, 27, 4, 12], ![25, 11, 16, 17, 12]),
    (![7, 26, 22, 31, 4], ![8, 3, 25, 12, 1]),
    (![1, 2, 4, 8, 16], ![1, 2, 4, 8, 16])]) i

private def pw4 (i : Fin 4) : List Bool :=
  (![
    [true, false, false, true, false, false, false, true, true],
    [false, true, false, true],
    [true, false, true, false, false, false],
    []]) i

private def fw4 (i : Fin 4) : Fin 6 → Fin 6 :=
  (![
    ![1, 3, 2, 0, 4, 5],
    ![2, 3, 0, 1, 4, 5],
    ![0, 3, 1, 2, 4, 5],
    ![0, 1, 2, 3, 4, 5]]) i

private def bw4 (i : Fin 4) : Fin 6 → Fin 6 :=
  (![
    ![3, 0, 2, 1, 4, 5],
    ![2, 3, 0, 1, 4, 5],
    ![0, 2, 3, 1, 4, 5],
    ![0, 1, 2, 3, 4, 5]]) i

private theorem inv4 : ∀ (i : Fin 4) (j : Fin 6),
    bw4 i (fw4 i j) = j ∧ fw4 i (bw4 i j) = j := by decide +kernel

private def pk4 (i : Fin 4) : P :=
  ⟨fw4 i, bw4 i, fun j ↦ (inv4 i j).1, fun j ↦ (inv4 i j).2⟩

private theorem pk_word4 (i : Fin 4) : pk4 i = (wp (pw4 i)).val := by
  apply Equiv.ext
  revert i
  decide +kernel

private def tr4 (i : Fin 4) : H :=
  ⟨pk4 i, (pk_word4 i).symm ▸ (wp (pw4 i)).property⟩

private def mb4 (i : Fin 4) : Mat :=
  (![(![28, 25, 15, 20, 6], ![4, 7, 17, 8, 5]),
    (![19, 29, 9, 23, 15], ![21, 7, 16, 25, 4]),
    (![26, 17, 6, 22, 9], ![5, 7, 1, 9, 21]),
    (![1, 2, 4, 8, 16], ![1, 2, 4, 8, 16])]) i

private def pw3 (i : Fin 3) : List Bool :=
  (![
    [false, false, true, false, true, false, false],
    [false, false, false, false, true, false, true, false, false, false, false],
    []]) i

private def fw3 (i : Fin 3) : Fin 6 → Fin 6 :=
  (![
    ![1, 2, 0, 3, 4, 5],
    ![2, 0, 1, 3, 4, 5],
    ![0, 1, 2, 3, 4, 5]]) i

private def bw3 (i : Fin 3) : Fin 6 → Fin 6 :=
  (![
    ![2, 0, 1, 3, 4, 5],
    ![1, 2, 0, 3, 4, 5],
    ![0, 1, 2, 3, 4, 5]]) i

private theorem inv3 : ∀ (i : Fin 3) (j : Fin 6),
    bw3 i (fw3 i j) = j ∧ fw3 i (bw3 i j) = j := by decide +kernel

private def pk3 (i : Fin 3) : P :=
  ⟨fw3 i, bw3 i, fun j ↦ (inv3 i j).1, fun j ↦ (inv3 i j).2⟩

private theorem pk_word3 (i : Fin 3) : pk3 i = (wp (pw3 i)).val := by
  apply Equiv.ext
  revert i
  decide +kernel

private def tr3 (i : Fin 3) : H :=
  ⟨pk3 i, (pk_word3 i).symm ▸ (wp (pw3 i)).property⟩

private def mb3 (i : Fin 3) : Mat :=
  (![(![2, 3, 12, 4, 27], ![17, 3, 21, 25, 1]),
    (![3, 1, 8, 12, 30], ![16, 18, 5, 9, 17]),
    (![1, 2, 4, 8, 16], ![1, 2, 4, 8, 16])]) i

private abbrev Row := Fin 6 × Fin 5 × Fin 4 × Fin 3

private def permOf (r : Row) : H := tr6 r.1 * tr5 r.2.1 * tr4 r.2.2.1 * tr3 r.2.2.2

private def matrixOf (r : Row) : Mat :=
  mulM (mulM (mulM (mb6 r.1) (mb5 r.2.1)) (mb4 r.2.2.1)) (mb3 r.2.2.2)

private def rowOf (p : H) : Row :=
  let i : Fin 6 := p.val.toFun 5
  let j : Fin 5 := ⟨(bw6 i (p.val.toFun 4)).val % 5, Nat.mod_lt _ (by decide)⟩
  let k : Fin 4 := ⟨(bw5 j (bw6 i (p.val.toFun 3))).val % 4, Nat.mod_lt _ (by decide)⟩
  let l : Fin 3 := ⟨(bw4 k (bw5 j (bw6 i (p.val.toFun 2)))).val % 3, Nat.mod_lt _ (by decide)⟩
  (i, j, k, l)

private def mat (a : H) : Mat := matrixOf (rowOf a)

private def edge (i : Fin 6) (j : Fin 5) (k : Fin 4) (l : Fin 3) (b : Bool) : Prop :=
  let left := mat (permOf (i, j, k, l) * genH b)
  let right := mulM (matrixOf (i, j, k, l)) (genM b)
  ∀ n : Fin 5, left.1 n = right.1 n ∧ left.2 n = right.2 n

private instance (i : Fin 6) (j : Fin 5) (k : Fin 4) (l : Fin 3) (b : Bool) :
    Decidable (edge i j k l b) := by unfold edge; infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check the 60 mixed-radix rows with this first digit in the kernel.
private theorem rowBatch0 (j : Fin 5) :
    ∀ (k : Fin 4) (l : Fin 3), rowOf (permOf (0, j, k, l)) = (0, j, k, l) := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check 120 right-generator edges, with columnwise equality in the kernel.
private theorem edgeBatch0 (j : Fin 5) : ∀ (k : Fin 4) (l : Fin 3) (b : Bool), edge 0 j k l b := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check the 60 mixed-radix rows with this first digit in the kernel.
private theorem rowBatch1 (j : Fin 5) :
    ∀ (k : Fin 4) (l : Fin 3), rowOf (permOf (1, j, k, l)) = (1, j, k, l) := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check 120 right-generator edges, with columnwise equality in the kernel.
private theorem edgeBatch1 (j : Fin 5) : ∀ (k : Fin 4) (l : Fin 3) (b : Bool), edge 1 j k l b := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check the 60 mixed-radix rows with this first digit in the kernel.
private theorem rowBatch2 (j : Fin 5) :
    ∀ (k : Fin 4) (l : Fin 3), rowOf (permOf (2, j, k, l)) = (2, j, k, l) := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check 120 right-generator edges, with columnwise equality in the kernel.
private theorem edgeBatch2 (j : Fin 5) : ∀ (k : Fin 4) (l : Fin 3) (b : Bool), edge 2 j k l b := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check the 60 mixed-radix rows with this first digit in the kernel.
private theorem rowBatch3 (j : Fin 5) :
    ∀ (k : Fin 4) (l : Fin 3), rowOf (permOf (3, j, k, l)) = (3, j, k, l) := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check 120 right-generator edges, with columnwise equality in the kernel.
private theorem edgeBatch3 (j : Fin 5) : ∀ (k : Fin 4) (l : Fin 3) (b : Bool), edge 3 j k l b := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check the 60 mixed-radix rows with this first digit in the kernel.
private theorem rowBatch4 (j : Fin 5) :
    ∀ (k : Fin 4) (l : Fin 3), rowOf (permOf (4, j, k, l)) = (4, j, k, l) := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check 120 right-generator edges, with columnwise equality in the kernel.
private theorem edgeBatch4 (j : Fin 5) : ∀ (k : Fin 4) (l : Fin 3) (b : Bool), edge 4 j k l b := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check the 60 mixed-radix rows with this first digit in the kernel.
private theorem rowBatch5 (j : Fin 5) :
    ∀ (k : Fin 4) (l : Fin 3), rowOf (permOf (5, j, k, l)) = (5, j, k, l) := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check 120 right-generator edges, with columnwise equality in the kernel.
private theorem edgeBatch5 (j : Fin 5) : ∀ (k : Fin 4) (l : Fin 3) (b : Bool), edge 5 j k l b := by
  fin_cases j <;> decide +kernel

private theorem row_perm : Function.LeftInverse rowOf permOf := by
  rintro ⟨i, j, k, l⟩
  fin_cases i
  · exact rowBatch0 j k l
  · exact rowBatch1 j k l
  · exact rowBatch2 j k l
  · exact rowBatch3 j k l
  · exact rowBatch4 j k l
  · exact rowBatch5 j k l

private theorem allEdges (i : Fin 6) (j : Fin 5) (k : Fin 4) (l : Fin 3) (b : Bool) :
    edge i j k l b := by
  fin_cases i
  · exact edgeBatch0 j k l b
  · exact edgeBatch1 j k l b
  · exact edgeBatch2 j k l b
  · exact edgeBatch3 j k l b
  · exact edgeBatch4 j k l b
  · exact edgeBatch5 j k l b

private theorem perm_row : Function.RightInverse rowOf permOf := by
  have hcard : Fintype.card Row = Fintype.card H := by
    rw [card_alternatingGroup (α := Fin 6)]
    simp only [Fintype.card_prod, Fintype.card_fin]
    decide
  have hs : Function.Surjective permOf :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨row_perm.injective, hcard⟩ |>.surjective
  exact row_perm.rightInverse_of_surjective hs

private theorem mat_edge (a : H) (b : Bool) : mat (a * genH b) = mulM (mat a) (genM b) := by
  have hp := perm_row a
  have h := allEdges (rowOf a).1 (rowOf a).2.1 (rowOf a).2.2.1 (rowOf a).2.2.2 b
  change ∀ n : Fin 5, (mat (permOf (rowOf a) * genH b)).1 n = (mulM (mat a) (genM b)).1 n ∧
    (mat (permOf (rowOf a) * genH b)).2 n = (mulM (mat a) (genM b)).2 n at h
  rw [hp] at h
  exact Prod.ext (funext fun n ↦ (h n).1) (funext fun n ↦ (h n).2)

private theorem idM_mul (a : Mat) : mulM idM a = a :=
  Prod.ext (funext fun i ↦ actB_id (a.1 i)) (funext fun i ↦ actB_id (a.2 i))

private theorem mat_one : mat 1 = idM := by
  have h : ∀ i : Fin 5, (mat 1).1 i = idB i ∧ (mat 1).2 i = idB i := by decide +kernel
  exact Prod.ext (funext fun i ↦ (h i).1) (funext fun i ↦ (h i).2)

private theorem mat_gen (b : Bool) : mat (genH b) = genM b := by
  simpa only [one_mul, mat_one, idM_mul] using mat_edge 1 b

private theorem wp_acc (w : List Bool) (a : H) : w.foldl (fun p b ↦ p * genH b) a = a * wp w := by
  induction w generalizing a with
  | nil => simp [wp]
  | cons b w ih =>
    change w.foldl (fun p c ↦ p * genH c) (a * genH b) =
      a * w.foldl (fun p c ↦ p * genH c) (1 * genH b)
    simp only [ih, one_mul, mul_assoc]

private theorem wp_cons (b : Bool) (w : List Bool) : wp (b :: w) = genH b * wp w := by
  change w.foldl (fun p c ↦ p * genH c) (1 * genH b) = _
  simpa only [one_mul] using wp_acc w (1 * genH b)

private theorem wp_append (w v : List Bool) : wp (w ++ v) = wp w * wp v := by
  change (w ++ v).foldl (fun a c ↦ a * genH c) 1 = _
  rw [List.foldl_append, wp_acc]
  rfl

private theorem trans_word6 (i : Fin 6) : tr6 i = wp (pw6 i) := Subtype.ext (pk_word6 i)
private theorem trans_word5 (i : Fin 5) : tr5 i = wp (pw5 i) := Subtype.ext (pk_word5 i)
private theorem trans_word4 (i : Fin 4) : tr4 i = wp (pw4 i) := Subtype.ext (pk_word4 i)
private theorem trans_word3 (i : Fin 3) : tr3 i = wp (pw3 i) := Subtype.ext (pk_word3 i)

private theorem mat_mul_word (a : H) (w : List Bool) :
    mat (a * wp w) = mulM (mat a) (mat (wp w)) := by
  induction w generalizing a with
  | nil => simp [wp, mat_one, mulM_id]
  | cons b w ih =>
    rw [wp_cons, ← mul_assoc, ih, ih, mat_edge, mat_gen, mulM_assoc]

private theorem mat_mul (a b : H) : mat (a * b) = mulM (mat a) (mat b) := by
  let r := rowOf b
  let w := pw6 r.1 ++ pw5 r.2.1 ++ pw4 r.2.2.1 ++ pw3 r.2.2.2
  have h : wp w = b := by
    simpa only [w, wp_append, ← trans_word6, ← trans_word5, ← trans_word4, ← trans_word3, mul_assoc,
      r, permOf] using perm_row b
  simpa only [h] using mat_mul_word a w

/-- Coordinates 1–5 and 6–10 of a binary column vector. -/
private structure Vec where
  low : Bits
  high : Bits
  deriving DecidableEq

private theorem vec_ext {x y : Vec} (hl : x.low = y.low) (hh : x.high = y.high) : x = y := by
  cases x; cases y; congr

private def vecMul (x y : Vec) : Vec := ⟨x.low ^^^ y.low, x.high ^^^ y.high⟩
private def vecOne : Vec := ⟨0#5, 0#5⟩

private instance : CommGroup Vec where
  mul := vecMul
  one := vecOne
  inv := id
  mul_assoc x y z :=
    vec_ext (BitVec.xor_assoc x.low y.low z.low) (BitVec.xor_assoc x.high y.high z.high)
  one_mul x := vec_ext BitVec.zero_xor BitVec.zero_xor
  mul_one x := vec_ext BitVec.xor_zero BitVec.xor_zero
  inv_mul_cancel x := vec_ext BitVec.xor_self BitVec.xor_self
  mul_comm x y := vec_ext (BitVec.xor_comm x.low y.low) (BitVec.xor_comm x.high y.high)

private def act (m : Mat) (v : Vec) : Vec := ⟨actB m.1 v.low, actB m.2 v.high⟩

private theorem act_mul (a b : Mat) (v : Vec) : act (mulM a b) v = act a (act b v) :=
  vec_ext (actB_comp a.1 b.1 v.low) (actB_comp a.2 b.2 v.high)

private theorem act_one (v : Vec) : act idM v = v := vec_ext (actB_id v.low) (actB_id v.high)

private def matAut (a : H) : MulAut Vec where
  toFun := act (mat a)
  invFun := act (mat a⁻¹)
  left_inv v := by rw [← act_mul, ← mat_mul, inv_mul_cancel, mat_one, act_one]
  right_inv v := by rw [← act_mul, ← mat_mul, mul_inv_cancel, mat_one, act_one]
  map_mul' x y := vec_ext (actB_xor (mat a).1 x.low y.low) (actB_xor (mat a).2 x.high y.high)

private def action : H →* MulAut Vec where
  toFun := matAut
  map_one' := MulEquiv.ext fun v ↦ by change act (mat 1) v = v; rw [mat_one, act_one]
  map_mul' a b := MulEquiv.ext fun v ↦ by
    change act (mat (a * b)) v = act (mat a) (act (mat b) v)
    rw [mat_mul, act_mul]

private abbrev G := Vec ⋊[action] H

private def q : Vec := ⟨21, 31⟩
private def exceptional : G := ⟨q, 1⟩

private def span : List Bits → List Bits
  | [] => [0#5]
  | c :: cs => let s := span cs; (s ++ s.map (c ^^^ ·)).eraseDups

private theorem mem_span_cons (c : Bits) (cs : List Bits) (u : Bits) :
    u ∈ span (c :: cs) ↔ u ∈ span cs ∨ ∃ t ∈ span cs, c ^^^ t = u := by simp [span]

private theorem span_induction (P : Bits → Prop) (h0 : P 0)
    (hx : ∀ {x y}, P x → P y → P (x ^^^ y)) (cs : List Bits)
    (hc : ∀ c ∈ cs, P c) {u : Bits} (hu : u ∈ span cs) : P u := by
  induction cs generalizing u with
  | nil =>
    obtain rfl : u = 0#5 := by simpa [span] using hu
    exact h0
  | cons c cs ih =>
    have ih' {v : Bits} := @ih (fun t ht ↦ hc t (List.mem_cons_of_mem _ ht)) v
    rcases (mem_span_cons c cs u).1 hu with h | ⟨t, ht, rfl⟩
    · exact ih' h
    · exact hx (hc c (by simp)) (ih' ht)

private theorem mem_span_pick (c u : Bits) (b : Bool) (cs : List Bits) (hu : u ∈ span cs) :
    pick b c ^^^ u ∈ span (c :: cs) := by
  apply (mem_span_cons _ _ _).2
  cases b
  · exact Or.inl (by simpa [pick] using hu)
  · exact Or.inr ⟨u, hu, rfl⟩

private def cols (m n : Block) : List Bits := List.ofFn m ++ List.ofFn n

private theorem mem_span_iff (m n : Block) (u : Bits) :
    u ∈ span (cols m n) ↔ ∃ s t, actB m s ^^^ actB n t = u := by
  constructor
  · apply span_induction (fun v ↦ ∃ s t, actB m s ^^^ actB n t = v)
    · refine ⟨0#5, 0#5, ?_⟩
      rw [show actB m 0#5 = 0#5 from actB_zero m, show actB n 0#5 = 0#5 from actB_zero n]
      rfl
    · rintro x y ⟨s, t, rfl⟩ ⟨s', t', rfl⟩
      refine ⟨s ^^^ s', t ^^^ t', ?_⟩
      simp only [actB_xor]
      ac_rfl
    · intro c hc
      simp only [cols, List.mem_append, List.mem_ofFn] at hc
      rcases hc with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact ⟨idB i, 0#5, by
          rw [actB_single, show actB n 0#5 = 0#5 from actB_zero n, BitVec.xor_zero]⟩
      · exact ⟨0#5, idB i, by
          rw [show actB m 0#5 = 0#5 from actB_zero m, actB_single, BitVec.zero_xor]⟩
  · rintro ⟨s, t, rfl⟩
    rw [actB, actB]
    simp only [BitVec.xor_assoc]
    change _ ∈ span [m 0, m 1, m 2, m 3, m 4, n 0, n 1, n 2, n 3, n 4]
    have h0 : (0#5 : Bits) ∈ span [] := by simp [span]
    have h := mem_span_pick (n 4) 0#5 (t.getLsbD 4) [] h0
    rw [BitVec.xor_zero] at h
    iterate 9 apply mem_span_pick
    exact h

private def bitsOf {α : Type} (xs : List α) (f : α → Nat) : Nat :=
  xs.foldr (fun x m ↦ 2 ^ f x ||| m) 0

private theorem testBit_bitsOf {α : Type} (xs : List α) (f : α → Nat) (i : Nat) :
    (bitsOf xs f).testBit i = true ↔ ∃ x ∈ xs, f x = i := by
  induction xs with
  | nil => simp [bitsOf]
  | cons x xs ih =>
    change ((2 ^ f x) ||| bitsOf xs f).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq, ih]
    simp [List.mem_cons, or_and_right, exists_or]

private def vectorIndex (x y : Bits) : Nat := x.toNat + 32 * y.toNat

private theorem vectorIndex_lt (x y : Bits) : vectorIndex x y < 1024 := by
  have hx := x.isLt
  have hy := y.isLt
  unfold vectorIndex
  omega

private theorem vectorIndex_eq {x y x' y' : Bits} :
    vectorIndex x y = vectorIndex x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    have hx := x.isLt
    have hy := y.isLt
    have hx' := x'.isLt
    have hy' := y'.isLt
    unfold vectorIndex at h
    exact ⟨BitVec.eq_of_toNat_eq (by omega), BitVec.eq_of_toNat_eq (by omega)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private def planeMask (lo hi : List Bits) : Nat :=
  hi.foldr (fun y m ↦ (bitsOf lo BitVec.toNat <<< (32 * y.toNat)) ||| m) 0

private theorem bit_planeMask (lo hi : List Bits) (x y : Bits) :
    (planeMask lo hi).testBit (vectorIndex x y) = true ↔ x ∈ lo ∧ y ∈ hi := by
  induction hi with
  | nil => simp [planeMask]
  | cons b bs ih =>
    change (((bitsOf lo BitVec.toNat <<< (32 * b.toNat)) ||| planeMask lo bs).testBit
      (vectorIndex x y) = true) ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.testBit_shiftLeft, Bool.and_eq_true,
      decide_eq_true_eq, testBit_bitsOf]
    have key : (32 * b.toNat ≤ vectorIndex x y ∧
        ∃ a ∈ lo, a.toNat = vectorIndex x y - 32 * b.toNat) ↔ x ∈ lo ∧ y = b := by
      constructor
      · rintro ⟨hle, a, ha, e⟩
        have ee : vectorIndex x y = vectorIndex a b := by unfold vectorIndex at *; omega
        obtain ⟨rfl, rfl⟩ := vectorIndex_eq.mp ee
        exact ⟨ha, rfl⟩
      · rintro ⟨hx, rfl⟩
        refine ⟨by unfold vectorIndex; omega, x, hx, ?_⟩
        unfold vectorIndex
        omega
    simp only [key, List.mem_cons, and_or_left]

private def unionMasks {α : Type} (xs : List α) (mask : α → Nat) : Nat :=
  xs.foldr (fun a m ↦ mask a ||| m) 0

private theorem bit_unionMasks {α : Type} (xs : List α) (mask : α → Nat) (i : Nat) :
    (unionMasks xs mask).testBit i = true ↔ ∃ a ∈ xs, (mask a).testBit i = true := by
  induction xs with
  | nil => simp [unionMasks]
  | cons a as ih =>
    change (mask a ||| unionMasks as mask).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    simp [List.mem_cons, or_and_right, exists_or]


/-- Commutator in the convention of Hatem–Siniora, equation (1). -/
private def comm {A : Type} [Group A] (a b : A) : A := a * b * a⁻¹ * b⁻¹

private theorem comm_conj {A : Type} [Group A] (g a b : A) :
    comm (g * a * g⁻¹) (g * b * g⁻¹) = g * comm a b * g⁻¹ := by
  unfold comm
  group

private theorem comm_swap {A : Type} [Group A] (a b : A) : comm b a = (comm a b)⁻¹ := by
  unfold comm
  group

private theorem vec_inv (x : Vec) : x⁻¹ = x := rfl

private theorem comm_right (x y : G) : (comm x y).right = comm x.right y.right := rfl

private theorem comm_left (x y : G) : (comm x y).left =
    x.left * action x.right y.left * action (x.right * y.right * x.right⁻¹) x.left *
      action (comm x.right y.right) y.left := by
  simp only [comm, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.inv_left, SemidirectProduct.inv_right, vec_inv]
  rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]

private def xorB (m n : Block) : Block := fun i ↦ m i ^^^ n i

private theorem pick_xor_val (b : Bool) (x y : Bits) :
    pick b (x ^^^ y) = pick b x ^^^ pick b y := by
  cases b <;> simp [pick]

private theorem actB_xorB (m n : Block) (v : Bits) : actB (xorB m n) v = actB m v ^^^ actB n v := by
  simp only [actB, xorB, pick_xor_val]
  ac_rfl

private def commCoeffs (a b : H) : Mat × Mat :=
  let d := mat (a * b * a⁻¹)
  let A := mat a
  let C := mat (comm a b)
  ((xorB idB d.1, xorB idB d.2), (xorB A.1 C.1, xorB A.2 C.2))

private theorem comm_vec (a b : H) (s t : Vec) :
    (comm (⟨s, a⟩ : G) ⟨t, b⟩).left =
      act (commCoeffs a b).1 s * act (commCoeffs a b).2 t := by
  rw [comm_left]
  apply vec_ext
  · change (((s.low ^^^ actB (mat a).1 t.low) ^^^ actB (mat (a * b * a⁻¹)).1 s.low) ^^^
      actB (mat (comm a b)).1 t.low) =
      actB (xorB idB (mat (a * b * a⁻¹)).1) s.low ^^^ actB (xorB (mat a).1 (mat (comm a b)).1) t.low
    simp only [actB_xorB, actB_id]
    ac_rfl
  · change (((s.high ^^^ actB (mat a).2 t.high) ^^^ actB (mat (a * b * a⁻¹)).2 s.high) ^^^
      actB (mat (comm a b)).2 t.high) =
      actB (xorB idB (mat (a * b * a⁻¹)).2) s.high ^^^
      actB (xorB (mat a).2 (mat (comm a b)).2) t.high
    simp only [actB_xorB, actB_id]
    ac_rfl

private def pairMask (a b : H) : Nat :=
  let (m, n) := commCoeffs a b
  planeMask (span (cols m.1 n.1)) (span (cols m.2 n.2))

private theorem bit_pairMask (a b : H) (v : Vec) :
    (pairMask a b).testBit (vectorIndex v.low v.high) = true ↔
      ∃ s t : Vec, (comm (⟨s, a⟩ : G) ⟨t, b⟩).left = v := by
  unfold pairMask
  rw [bit_planeMask, mem_span_iff, mem_span_iff]
  simp only [comm_vec]
  constructor
  · rintro ⟨⟨s₁, t₁, h₁⟩, s₂, t₂, h₂⟩
    exact ⟨⟨s₁, s₂⟩, ⟨t₁, t₂⟩, vec_ext h₁ h₂⟩
  · rintro ⟨s, t, h⟩
    exact ⟨⟨s.low, t.low, congrArg Vec.low h⟩, s.high, t.high, congrArg Vec.high h⟩

private theorem exists_word (a : H) : ∃ w : List Bool, wp w = a := by
  let r := rowOf a
  refine ⟨pw6 r.1 ++ pw5 r.2.1 ++ pw4 r.2.2.1 ++ pw3 r.2.2.2, ?_⟩
  simpa only [wp_append, ← trans_word6, ← trans_word5, ← trans_word4, ← trans_word3, mul_assoc,
    r, permOf] using perm_row a

private theorem q_gen (b : Bool) : action (genH b) q = q := by
  change act (mat (genH b)) q = q
  rw [mat_gen]
  cases b <;> rfl

private theorem q_fixed (a : H) : action a q = q := by
  obtain ⟨w, rfl⟩ := exists_word a
  induction w with
  | nil => change action 1 q = q; rw [map_one, MulAut.one_apply]
  | cons b w ih => rw [wp_cons, map_mul, MulAut.mul_apply, ih, q_gen]

private theorem exceptional_commute (g : G) : Commute g exceptional := by
  rcases g with ⟨v, a⟩
  apply SemidirectProduct.ext
  · simp [exceptional, q_fixed, mul_comm]
  · simp [exceptional]

private theorem conj_exceptional (g : G) : g * exceptional * g⁻¹ = exceptional := by
  rw [(exceptional_commute g).eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem inv_exceptional : exceptional⁻¹ = exceptional := by
  apply SemidirectProduct.ext <;> simp [exceptional, vec_inv]

private def rowIndex (r : Row) : Nat :=
  60 * r.1.val + 12 * r.2.1.val + 3 * r.2.2.1.val + r.2.2.2.val

private theorem rowIndex_inj : Function.Injective rowIndex := by
  rintro ⟨i, j, k, l⟩ ⟨i', j', k', l'⟩ h
  have hi := i.isLt
  have hi' := i'.isLt
  have hj := j.isLt
  have hj' := j'.isLt
  have hk := k.isLt
  have hk' := k'.isLt
  have hl := l.isLt
  have hl' := l'.isLt
  change 60 * i.val + 12 * j.val + 3 * k.val + l.val =
    60 * i'.val + 12 * j'.val + 3 * k'.val + l'.val at h
  have e₁ : i = i' := Fin.ext (by omega)
  have e₂ : j = j' := Fin.ext (by omega)
  have e₃ : k = k' := Fin.ext (by omega)
  have e₄ : l = l' := Fin.ext (by omega)
  rw [e₁, e₂, e₃, e₄]

private def pIndex (p : H) : Nat := rowIndex (rowOf p)

private theorem pIndex_inj : Function.Injective pIndex := rowIndex_inj.comp perm_row.injective

private theorem pIndex_lt (p : H) : pIndex p < 360 := by
  rcases hr : rowOf p with ⟨i, j, k, l⟩
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  have hl := l.isLt
  simp only [pIndex, hr, rowIndex]
  omega

private def indices (n : Nat) : List (Fin n) := List.ofFn id

private theorem mem_indices {n : Nat} (i : Fin n) : i ∈ indices n := by
  simp [indices]

private def rows : List Row := (indices 6).flatMap fun i ↦ (indices 5).flatMap fun j ↦
  (indices 4).flatMap fun k ↦ (indices 3).map fun l ↦ (i, j, k, l)

private theorem mem_rows (r : Row) : r ∈ rows := by
  rcases r with ⟨i, j, k, l⟩
  exact List.mem_flatMap.2 ⟨i, mem_indices i, List.mem_flatMap.2 ⟨j, mem_indices j,
    List.mem_flatMap.2 ⟨k, mem_indices k, List.mem_map.2 ⟨l, mem_indices l, rfl⟩⟩⟩⟩

private abbrev Word := List Bool
private abbrev WPair := Word × Word
private abbrev s := false
private abbrev e := true

/-- Seven representatives, in the order identity, 3, 2·2, 5, 5, 4·2, and 3·3.
The two 5-cycle classes are kept separate. -/
private def representative : Fin 7 → Word :=
  ![[],
    [e],
    [s, s, s, s, e, s, e, e],
    [e, s, s, s, e, s, s],
    [e, s, s, s, e, s, s, e],
    [s, e, e, s, e, s, s, e, s],
    [s, s, e, s, e, s, s, e]]

/-- Positive word pairs whose commutator images cover each indicated fiber.
The identity fiber is covered except for the exceptional vector. -/
private def pairWords : Fin 7 → List WPair :=
  ![-- identity
    [([], [e, s, s, s, e, s, s]),
     ([], [s]),
     ([], [s, e, e]),
     ([], [e, e, s]),
     ([], [e, e, s, s, e, s, s, s]),
     ([], [s, s, s, e, s, e, e, s, s, e]),
     ([e], [s, s, e, s, e, s, s]),
     ([e, s, e, s, s, e, s, e], [s, s, s, e, s, e, e, s, s, e, e]),
     ([s, s, s, s, e, s, e], [s, s, e, s, s, s]),
     ([e, e, s, e, s, s, e, s], [s, e, s, e, e, s, e, s, s, s]),
     ([s, s, s, s, e, s, e, e], [s, e, s, e, s, s, e, e]),
     ([s, s, s, s, e, e, s, e], [e, s, e, e, s, e, s, s, s]),
     ([s, s, s, e, s, s], [e, s, e, s, s, s, s]),
     ([s, e, s, s, e, s], [s, e, s, e, e, s, e, s, s, e, s, e]),
     ([s, e, e, s, e, s, s, s], [s, s, e, e, s, e, s, e]),
     ([s, s, s, e, s, e, e, s, e], [s, e, s, s, s, s, e, e]),
     ([s, s, e, s, e, e, s, e, s], [s, e, s, e]),
     ([s, s, s, s, e, s], [s, e, s, e, s, s, s]),
     ([s, s, s, e, s, e, e, s, e], [s, s, e, s, e, s, s, s, s]),
     ([s, s, s, s, e, s, e, e], [s, e, e, s, e, s, s, s]),
     ([s, e, s, e, s, s, e, e], [s, e, e, s, e, s, s, s, e]),
     ([e, s, s, s, e, s, e, e, s], [s, e, s, e, e, s, s, e]),
     ([e, s, s, s, e, s, e, e, s], [e, s, e, s, s, s, s, e]),
     ([s, s, s, e, s, e, e, s], [e, s, e, s, s, e, e, s]),
     ([s, s, s, e, s, e, e, s], [s, s, e, s, e, s, e, e]),
     ([e, s, e, s, s, e, s, e, e], [e, e, s, e, s, s, e, s, e]),
     ([e, s, e, s, s, e, s, e, e], [s, s, e, e, s, e, s, s, e, e, s]),
     ([s, s, e, s, e, s, s, s, s], [s, e, s, s, s, e, e, s, e, e]),
     ([e, s, e, s, s, e, e, s], [s, s, e, s, s, e]),
     ([e, e, s, e, s, s, e, s, e], [s, e, s, e, e, s, e, s, s, e, s]),
     ([e, e, s, e, s, s, e, e, s, e, e], [e, s, s, e, s, s]),
     ([s, e, s, e, e, s, s, e], [e, s, e, s, s, s, e, e, s, e]),
     ([s, s, s, e, e, s, e, s], [s, e, e, s, s, s, e, s, e, e]),
     ([s, e, s, s, e, e, s, e], [s, s, s, e, s, e, s, s, s]),
     ([e, s, e, e, s, e, s, s, s], [s, s, s, s, e, s, e, s, s]),
     ([s, e, e, s, e, s, s, s, e], [e, s, e, e, s, s, e, s]),
     ([e, s, e, e, s, e, s, s, e, s, e], [e, s, e, s]),
     ([s, s, e, s, e, e, s, s], [e, e, s, e, s, e, e]),
     ([s, s, e, e, s, e, s, s, e, e, s], [s, s, e, s, s, e]),
     ([s, e, s, e, e, s, e, s, s, e, s, e], [s, s, s, e, s, e, s, s, s]),
     ([s, e, s, e, e, s, e, s, s, e, s], [e, s, e, s, s, s, e, e, s, e]),
     ([e, s, e, s, s, s, s, e], [s, s, e, s, e, s, e, e])],
    -- one 3-cycle
    [([s, s, s, s, e, s, e], [e, s, e, s, s, e, s]),
     ([s, s, s, s, e, s, e], [s, e, e, s, e, s, s, s, e]),
     ([s, s, s, s, e, s, e], [e, s, e, s, s, s, s, e, e])],
    -- double transposition
    [([e], [s, s, s, e, s, e, s, s, s, s])],
    -- first 5-cycle class
    [([e], [s, e, s, e, e, s, e, e])],
    -- second 5-cycle class
    [([e, e], [s, e, s, s])],
    -- a 4-cycle and a disjoint transposition
    [([s, s, s, s, e, s, e, e], [e, s, e, s, e])],
    -- two disjoint 3-cycles
    [([e, s, s, s, e, s, e, e, s], [s, s, s, s, e, s, s]),
     ([e, s, s, s, e, s, e, e, s], [s, s, s, e, s, e, e]),
     ([e], [s, s, e, e, s]),
     ([s, s, s, e, s, e, e, s, e], [s, e, s, e, s, s, e, e, s]),
     ([s, s, s, e, s, e, e, s], [s, e, s, s, s, e, s, s])]]


private def rep (i : Fin 7) : H := wp (representative i)

private theorem rep_zero : rep 0 = 1 := rfl

private def orbitMask (i : Fin 7) : Nat := bitsOf rows fun r ↦
  let a := permOf r
  pIndex (a * rep i * a⁻¹)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Compute the union of seven quotient conjugacy orbits in the kernel.
private theorem orbit_cover : unionMasks (indices 7) orbitMask = 2^360 - 1 := by decide +kernel

private theorem quotient_conjugacy (p : H) : ∃ (i : Fin 7) (a : H), p = a * rep i * a⁻¹ := by
  have h : (unionMasks (indices 7) orbitMask).testBit (pIndex p) = true := by
    rw [orbit_cover, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (pIndex_lt p)
  obtain ⟨i, _, hi⟩ := (bit_unionMasks _ _ _).1 h
  obtain ⟨r, _, hr⟩ := (testBit_bitsOf _ _ _).1 hi
  exact ⟨i, permOf r, (pIndex_inj hr).symm⟩

private def correctPair (i : Fin 7) (p : WPair) : Bool :=
  pIndex (comm (wp p.1) (wp p.2)) == pIndex (rep i)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Check the quotient commutator of each selected word pair in the kernel.
private theorem pairs_correct (i : Fin 7) : (pairWords i).all (correctPair i) = true := by
  fin_cases i <;> decide +kernel

private theorem pair_quotient {i : Fin 7} {p : WPair} (h : p ∈ pairWords i) :
    comm (wp p.1) (wp p.2) = rep i := by
  apply pIndex_inj
  exact beq_iff_eq.1 (List.all_eq_true.1 (pairs_correct i) p h)

private def coverageMask (i : Fin 7) : Nat :=
  unionMasks (pairWords i) fun p ↦ pairMask (wp p.1) (wp p.2)

private def expectedMask (i : Fin 7) : Nat :=
  (2^1024 - 1) ^^^ (if i = 0 then 2^1013 else 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
-- Compute both five-dimensional spans and merge the masks in the kernel.
private theorem coverage_masks (i : Fin 7) : coverageMask i = expectedMask i := by
  fin_cases i <;> decide +kernel

private theorem q_index : vectorIndex q.low q.high = 1013 := rfl

private theorem expected_bit (i : Fin 7) (v : Vec) (h : i = 0 → v ≠ q) :
    (expectedMask i).testBit (vectorIndex v.low v.high) = true := by
  have hlt := vectorIndex_lt v.low v.high
  unfold expectedMask
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, decide_eq_true hlt]
  split
  · rename_i hi
    have hn : 1013 ≠ vectorIndex v.low v.high := by
      intro he
      rw [← q_index] at he
      obtain ⟨hl, hh⟩ := vectorIndex_eq.1 he.symm
      exact h hi (vec_ext hl hh)
    simp only [Nat.testBit_two_pow, decide_eq_false hn, Bool.xor_false]
  · simp only [Nat.zero_testBit, Bool.xor_false]

private theorem covered_rep (i : Fin 7) (v : Vec) (h : i = 0 → v ≠ q) :
    ∃ x y : G, comm x y = ⟨v, rep i⟩ := by
  have hb := expected_bit i v h
  rw [← coverage_masks] at hb
  obtain ⟨p, hp, hbit⟩ := (bit_unionMasks _ _ _).1 hb
  obtain ⟨u, w, hvec⟩ := (bit_pairMask _ _ _).1 hbit
  refine ⟨⟨u, wp p.1⟩, ⟨w, wp p.2⟩, SemidirectProduct.ext hvec ?_⟩
  rw [comm_right]
  exact pair_quotient hp

private def exclusionCheck (i : Fin 7) (r : Row) : Prop :=
  pIndex (comm (rep i) (permOf r)) = pIndex 1 → (pairMask (rep i) (permOf r)).testBit 1013 = false

private instance (i : Fin 7) (r : Row) : Decidable (exclusionCheck i r) := by
  unfold exclusionCheck
  infer_instance

/- For a nonidentity first component only the centralizer can contribute to the identity
fiber. The implication skips all other rows before inspecting the vector spans. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check the centralizer of this quotient representative in the kernel.
private theorem exclusionBatch1 (i : Fin 6) (j : Fin 5) :
    ∀ (k : Fin 4) (l : Fin 3), exclusionCheck 1 (i, j, k, l) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check the centralizer of this quotient representative in the kernel.
private theorem exclusionBatch2 (i : Fin 6) (j : Fin 5) :
    ∀ (k : Fin 4) (l : Fin 3), exclusionCheck 2 (i, j, k, l) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check the centralizer of this quotient representative in the kernel.
private theorem exclusionBatch3 (i : Fin 6) (j : Fin 5) :
    ∀ (k : Fin 4) (l : Fin 3), exclusionCheck 3 (i, j, k, l) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check the centralizer of this quotient representative in the kernel.
private theorem exclusionBatch4 (i : Fin 6) (j : Fin 5) :
    ∀ (k : Fin 4) (l : Fin 3), exclusionCheck 4 (i, j, k, l) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check the centralizer of this quotient representative in the kernel.
private theorem exclusionBatch5 (i : Fin 6) (j : Fin 5) :
    ∀ (k : Fin 4) (l : Fin 3), exclusionCheck 5 (i, j, k, l) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Check the centralizer of this quotient representative in the kernel.
private theorem exclusionBatch6 (i : Fin 6) (j : Fin 5) :
    ∀ (k : Fin 4) (l : Fin 3), exclusionCheck 6 (i, j, k, l) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem exclusion_all (i : Fin 7) (h : i ≠ 0) (j : Fin 6) (k : Fin 5)
    (l : Fin 4) (m : Fin 3) : exclusionCheck i (j, k, l, m) := by
  fin_cases i
  · exact False.elim (h rfl)
  · exact exclusionBatch1 j k l m
  · exact exclusionBatch2 j k l m
  · exact exclusionBatch3 j k l m
  · exact exclusionBatch4 j k l m
  · exact exclusionBatch5 j k l m
  · exact exclusionBatch6 j k l m


private theorem excluded_rep (i : Fin 7) (hi : i ≠ 0) (b : H) (hb : comm (rep i) b = 1) :
    (pairMask (rep i) b).testBit 1013 = false := by
  have h := exclusion_all i hi (rowOf b).1 (rowOf b).2.1 (rowOf b).2.2.1 (rowOf b).2.2.2
  change pIndex (comm (rep i) (permOf (rowOf b))) = pIndex 1 →
    (pairMask (rep i) (permOf (rowOf b))).testBit 1013 = false at h
  rw [perm_row b] at h
  exact h (congrArg pIndex hb)

private theorem exclude_nontrivial_left (x y : G) (hn : x.right ≠ 1) : comm x y ≠ exceptional := by
  intro hxy
  obtain ⟨i, a, ha⟩ := quotient_conjugacy x.right
  have hi : i ≠ 0 := by
    intro h
    subst i
    exact hn (by simpa [rep_zero] using ha)
  let z : G := SemidirectProduct.inr a⁻¹
  let x' := z * x * z⁻¹
  let y' := z * y * z⁻¹
  have hr : x'.right = rep i := by simp [x', z, ha, mul_assoc]
  have hc : comm x' y' = exceptional := by
    change comm (z * x * z⁻¹) (z * y * z⁻¹) = exceptional
    rw [comm_conj, hxy, conj_exceptional]
  have hp : comm (rep i) y'.right = 1 := by
    rw [← hr, ← comm_right, hc]
    rfl
  have hv : (comm (⟨x'.left, rep i⟩ : G) ⟨y'.left, y'.right⟩).left = q := by
    have ha' : (⟨x'.left, rep i⟩ : G) = x' := SemidirectProduct.ext rfl hr.symm
    rw [ha']
    change (comm x' y').left = q
    rw [hc]
    rfl
  have hbit := (bit_pairMask (rep i) y'.right q).2 ⟨x'.left, y'.left, hv⟩
  rw [q_index, excluded_rep i hi y'.right hp] at hbit
  contradiction

private theorem exceptional_excluded (x y : G) : comm x y ≠ exceptional := by
  by_cases hx : x.right = 1
  · by_cases hy : y.right = 1
    · rcases x with ⟨u, a⟩
      rcases y with ⟨v, b⟩
      change a = 1 at hx
      change b = 1 at hy
      subst a
      subst b
      have hz : comm u v = 1 := by
        unfold comm
        rw [mul_comm u v, mul_assoc v, mul_inv_cancel, mul_one, mul_inv_cancel]
      have hp : comm (⟨u, 1⟩ : G) ⟨v, 1⟩ = 1 := by
        change comm (SemidirectProduct.inl u : G) (SemidirectProduct.inl v) = 1
        simpa only [comm, map_mul, map_inv, map_one] using
          congrArg (SemidirectProduct.inl : Vec →* G) hz
      rw [hp]
      intro he
      have this : (1 : Vec) = q := congrArg SemidirectProduct.left he
      exact (show (1 : Vec) ≠ q by decide +kernel) this
    · intro h
      apply exclude_nontrivial_left y x hy
      rw [comm_swap, h, inv_exceptional]
  · exact exclude_nontrivial_left x y hx

private theorem covered (g : G) (hg : g ≠ exceptional) : ∃ x y : G, comm x y = g := by
  obtain ⟨i, a, ha⟩ := quotient_conjugacy g.right
  let z : G := SemidirectProduct.inr a
  let g' := z⁻¹ * g * z
  have hr : g'.right = rep i := by simp [g', z, ha, mul_assoc]
  have g'_conj : z * g' * z⁻¹ = g := by dsimp [g']; group
  have hv : i = 0 → g'.left ≠ q := by
    intro h hl
    have he : g' = exceptional := SemidirectProduct.ext hl (hr.trans (h ▸ rep_zero))
    apply hg
    rw [← g'_conj, he, conj_exceptional]
  obtain ⟨x, y, hc⟩ := covered_rep i g'.left hv
  refine ⟨z * x * z⁻¹, z * y * z⁻¹, ?_⟩
  have he : (⟨g'.left, rep i⟩ : G) = g' := SemidirectProduct.ext rfl hr.symm
  rw [comm_conj, hc, he, g'_conj]

private theorem commutator_iff_ne (g : G) :
    (∃ x y : G, g = x⁻¹ * y⁻¹ * x * y) ↔ g ≠ exceptional := by
  constructor
  · rintro ⟨x, y, rfl⟩
    simpa [comm] using exceptional_excluded x⁻¹ y⁻¹
  · intro h
    obtain ⟨x, y, hxy⟩ := covered g h
    exact ⟨x⁻¹, y⁻¹, by simpa [comm] using hxy.symm⟩

private def bitsEquiv : Bits ≃ Fin 32 where
  toFun := BitVec.toFin
  invFun := @BitVec.ofFin 5
  left_inv x := by cases x; rfl
  right_inv _ := rfl

private def vecEquiv : Vec ≃ Fin 32 × Fin 32 where
  toFun v := (bitsEquiv v.low, bitsEquiv v.high)
  invFun p := ⟨bitsEquiv.symm p.1, bitsEquiv.symm p.2⟩
  left_inv _ := vec_ext (bitsEquiv.symm_apply_apply _) (bitsEquiv.symm_apply_apply _)
  right_inv _ := Prod.ext (bitsEquiv.apply_symm_apply _) (bitsEquiv.apply_symm_apply _)

private def groupEquiv : G ≃ (Fin 32 × Fin 32) × H :=
  SemidirectProduct.equivProd.trans (Equiv.prodCongr vecEquiv (Equiv.refl H))

private theorem finiteG : Finite G := Finite.of_equiv _ groupEquiv.symm

private theorem group_card : Nat.card G = 368640 := by
  rw [Nat.card_congr groupEquiv, Nat.card_prod, Nat.card_prod, nat_card_alternatingGroup]
  simp only [Nat.card_fin]
  decide

private theorem noncommutators_eq_singleton :
    {g : G | ¬ ∃ x y : G, g = x⁻¹ * y⁻¹ * x * y} = {exceptional} := by
  ext g
  simp [commutator_iff_ne]

end ProductCertificate

@[expose] public section

namespace MathlibExt.GroupTheory.ExactlyOneNoncommutatorKourovka17Problem76Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 17.76 (D. MacHale). UnsolvedMath record
UM-00701378 (`KOU-17.76`), dataset ulamai/UnsolvedMath v1.8.0.

A commutator is an element `x⁻¹ y⁻¹ x y`; the target asks for a finite group of order greater than
`2` whose set of non-commutators has exactly one element (`Set.ncard`).
-/

/-- **Kourovka Problem 17.76 (finite groups with exactly one non-commutator).** This is the
statement that there is a finite group $G$ of order greater than $2$ in which exactly one element is
not a commutator, that is, not of the form $x^{-1}y^{-1}xy$ with $x, y \in G$. -/
def exactlyOneNoncommutator : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G), 2 < Nat.card G ∧
    {g : G | ¬ ∃ x y : G, g = x⁻¹ * y⁻¹ * x * y}.ncard = 1

/--
**A finite group with exactly one non-commutator.** There is a finite group $G$ of order greater
than $2$ in which exactly one element is not a commutator, that is, not of the form $x^{-1}y^{-1}xy$
with $x, y \in G$.

Resolved true: Skresanov constructs an infinite series of finite groups with exactly one element
that is not a commutator, the smallest of order 16609443840, and Hatem and Siniora find two such
groups of order 368640, the smallest possible order. The Kourovka Notebook (21st issue) answers
17.76 "Yes".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 17.76 (D. MacHale); resolution: S.
V. Skresanov, Siberian Electron. Math. Rep. 23 (2026), 603-607 (preprint On finite groups with
exactly one noncommutator, arXiv:2509.17587); O. Hatem and D. Siniora, Int. J. Group Theory 15
(2026), 161-167 (preprint A group with exactly one noncommutator, arXiv:2511.00541), Skresanov,
abstract (an infinite series of such groups, the smallest of order 16609443840); Hatem-Siniora,
abstract (two non-isomorphic groups of order 368640, the smallest order); the Kourovka Notebook
(21st issue) marks 17.76 solved (Yes, such groups do exist, and there are infinitely many examples),
https://arxiv.org/abs/2509.17587.
-/
public theorem exactlyOneNoncommutator_holds : exactlyOneNoncommutator := by
  refine ⟨ProductCertificate.G, inferInstance, ProductCertificate.finiteG, ?_, ?_⟩
  · rw [ProductCertificate.group_card]
    decide
  · rw [ProductCertificate.noncommutators_eq_singleton, Set.ncard_singleton]

end MathlibExt.GroupTheory.ExactlyOneNoncommutatorKourovka17Problem76Wanted
