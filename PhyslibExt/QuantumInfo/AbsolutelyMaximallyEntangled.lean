/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/OpenQuantumProblems/35.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
public import Mathlib.Tactic.Lemma
public import Mathlib.Tactic.NormNum.Prime
public import MathlibExt.Algebra.BigOperators.SeparableSum
public import MathlibExt.Analysis.Fourier.ZModAddCharSum
public import MathlibExt.Data.Finset.PasteSplit
public import MathlibExt.LinearAlgebra.Matrix.DetFinSmall

@[expose] public section

/-!
# An absolutely maximally entangled state of nine ten-level systems

A graph-state construction of an `AME(9, 10)` state, answering Open Quantum Problem 35 for
`(n, d) = (9, 10)`

## i. Overview

A pure state of `n` parties with local dimension `d` is *absolutely maximally entangled*
(`AME(n, d)`) when the reduced density matrix of every set of `⌊n / 2⌋` parties is maximally
mixed. Open Quantum Problem 35 asks for which `(n, d)` such a state exists;
`AME(9, 10)` was one of the open entries.

This file builds one. Writing the local dimension as `10 = 2 × 5`, a computational basis
state of one party splits into a qubit part and a qudit part (`bitPart`, `quintPart`). The
amplitude `ameAmplitude` is the uniform superposition, over the two logical qubits
`a : Fin 2 → ZMod 2`, of the product of two graph-state phases: a `ZMod 2` phase for the
nine-cycle graph `q2Cycle` with the logical labels `q2Label`, and a `ZMod 5` phase for the
ten-vertex circulant graph `q5Graph` with the logical letter `q5Logical` inserted in
position `0`. The reductions are computed with additive-character orthogonality
(`MetaMathlibExt.sum_stdAddChar_dot`); the two conditions that make every four-party
reduction maximally mixed are a minimum-weight bound for the `ZMod 2` code
(`q2Cycle_subgroup_minWeight`) and the invertibility of every `5 × 5` cut matrix of
`q5Graph` (`q5CutMatrix_det`), both checked by the kernel.

## ii. Key results

- `OpenQuantumProblem35.IsAME`, `OpenQuantumProblem35.ExistsAME`: absolute maximal
  entanglement of a pure state, and its existence for given `(n, d)`.
- `OpenQuantumProblem35.ameState`: the graph state constructed here.
- `OpenQuantumProblem35.ame_9_10_open`: an `AME(9, 10)` state exists.

## iii. Table of contents

- A. States, reductions, and absolute maximal entanglement
- B. The `ZMod 5` circulant graph on ten vertices and its cuts
- C. The `ZMod 2` nine-cycle graph and its code
- D. Characters, local splitting, and graph phases
- E. The state and its normalisation
- F. Four-party reductions and the main result

## iv. References

- Open Quantum Problems, Problem 35,
  <https://oqp.iqoqi.oeaw.ac.at/existence-of-absolutely-maximally-entangled-pure-states>
- W. Helwig, W. Cui, A. Riera, J. I. Latorre, H.-K. Lo, *Absolute Maximal Entanglement and
  Quantum Secret Sharing*, Phys. Rev. A 86, 052335 (2012), arXiv:1204.2289.
- D. Goyeneche, D. Alsina, J. I. Latorre, A. Riera, K. Życzkowski, *Absolutely Maximally
  Entangled states, combinatorial designs and multi-unitary matrices*, Phys. Rev. A 92,
  032316 (2015), arXiv:1506.08857.
- G. Rajchel-Mieldzioć, R. Bistroń, A. Rico, A. Lakshminarayan, K. Życzkowski, *Absolutely
  maximally entangled pure states of multipartite quantum systems*, arXiv:2508.04777 (2025).

## Source and provenance

`Config`, `StateVector`, `mkStateVector`, `IsNormalized`, `permuteConfig`, `permuteState`,
`combineFirst`, `reducedDensityFirst`, `maximallyMixed`, `HasMaximallyMixedFirstReduction`,
`IsAME`, `ExistsAME`, `IsConstantConfig` and the statement of `ame_9_10_open` are copied
verbatim from `FormalConjectures/OpenQuantumProblems/35.lean` of
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures);
`ame_9_10_open_statement` is a `Prop`-valued abbreviation for `ExistsAME 9 10`, added by
this development. The statement carried the Formal Conjectures attribute
`@[category research open, AMS 5 15 81 94]` at the revision this development was written
against; at commit `d8d031d4998c78575159ccab9a7a9e95ce043883` upstream records it as
`research solved`, citing a Lean proof derived from
these Atlas proofs. The Formal Conjectures attributes are dropped here because this
repository does not depend on `FormalConjecturesUtil`; nothing else in the statement is
changed. Following this repository's `PhyslibExt` convention, `ame_9_10_open` is stated with
`lemma` rather than `theorem`, which does not change its name or statement.

General-purpose helpers of the original development were moved to `MathlibExt`:
small-matrix determinants (`MathlibExt.LinearAlgebra.Matrix.DetFinSmall`), gluing and
splitting functions along a finset (`MathlibExt.Data.Finset.PasteSplit`), additive-character
sums over `ZMod N` (`MathlibExt.Analysis.Fourier.ZModAddCharSum`) and separable multiple
sums (`MathlibExt.Algebra.BigOperators.SeparableSum`); they now live in the
`MetaMathlibExt` namespace, which this module opens.
-/

open scoped BigOperators

namespace OpenQuantumProblem35

open MetaMathlibExt

/-! ## A. States, reductions, and absolute maximal entanglement -/




/-- A computational-basis configuration of $n$ parties with local dimension $d$. -/
abbrev Config (n d : ℕ) := Fin n → Fin d


/-- A vector of the finite-dimensional Hilbert space spanned by the computational basis
`Config n d`. It is an arbitrary vector: normalisation is the separate condition
`IsNormalized`. -/
abbrev StateVector (n d : ℕ) := EuclideanSpace ℂ (Config n d)


/-- Build a state vector from its computational-basis amplitudes. -/
abbrev mkStateVector {n d : ℕ} (ψ : Config n d → ℂ) : StateVector n d :=
  WithLp.toLp 2 ψ


/-- A state vector can be evaluated on a computational-basis configuration to read its
amplitude. -/
instance {n d : ℕ} : CoeFun (StateVector n d) (fun _ => Config n d → ℂ) where
  coe ψ := ψ.ofLp


/-- A state vector is normalized if it has $L^2$ norm $1$. -/
def IsNormalized {n d : ℕ} (ψ : StateVector n d) : Prop :=
  ‖ψ‖ = 1


/-- Permute the parties of a configuration: party `i` of the result carries the letter of
party `π i` of `x`. -/
def permuteConfig {n d : ℕ} (π : Equiv.Perm (Fin n)) (x : Config n d) : Config n d :=
  fun i => x (π i)


/-- Permute the parties of a state: the amplitude of the result on `x` is the amplitude of
`ψ` on `permuteConfig π x`. -/
def permuteState {n d : ℕ} (π : Equiv.Perm (Fin n)) (ψ : StateVector n d) : StateVector n d :=
  mkStateVector fun x => ψ (permuteConfig π x)





/-- For $m \le n$, assemble a configuration of all $n$ parties from a configuration `x` of
the first $m$ and a configuration `y` of the remaining $n - m$: party $i < m$ carries
`x i` and party $i \ge m$ carries `y (i - m)` (all indices zero-based). -/
def combineFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) : Config n d :=
  fun i =>
    if hi : i.1 < m then
      x ⟨i.1, hi⟩
    else
      y ⟨i.1 - m, by
        have him : m ≤ i.1 := Nat.le_of_not_gt hi
        omega⟩









/-- For $m \le n$ and an arbitrary vector `ψ` (zero included), the partial trace of
$\psi\psi^*$ over the last $n - m$ parties: the entry at `(x, y)` is
$\sum_z \psi(x, z) \overline{\psi(y, z)}$, where `(x, z)` is `combineFirst m hm x z`. It is a
density matrix (positive semidefinite of trace $1$) exactly when `ψ` is normalized; in
general its trace is $\lVert\psi\rVert^2$. -/
noncomputable def reducedDensityFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n) (ψ : StateVector n d) :
    Matrix (Config m d) (Config m d) ℂ :=
  fun x y =>
    ∑ z : Config (n - m) d,
      ψ (combineFirst (n := n) (d := d) m hm x z) *
        star (ψ (combineFirst (n := n) (d := d) m hm y z))


/-- The maximally mixed state of $m$ parties of local dimension $d$: the reciprocal of the
number of configurations `Fintype.card (Config m d)` (that is, $d^m$) times the identity
matrix. When the basis is empty ($d = 0 < m$) the matrix is the empty matrix, of trace
$0$: there is then no trace-one state. -/
noncomputable def maximallyMixed (m d : ℕ) :
    Matrix (Config m d) (Config m d) ℂ :=
  ((Fintype.card (Config m d) : ℂ)⁻¹) •
    (1 : Matrix (Config m d) (Config m d) ℂ)


/-- For $m \le n$, the reduced matrix `reducedDensityFirst m hm ψ` of the first $m$ parties
equals `maximallyMixed m d`. The vector `ψ` is arbitrary; normalisation is required
separately in `IsAME`. -/
def HasMaximallyMixedFirstReduction {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (ψ : StateVector n d) : Prop :=
  reducedDensityFirst (n := n) (d := d) m hm ψ = maximallyMixed m d














/-- A state is *absolutely maximally entangled* when it is normalized and, after any
permutation of the parties, the reduction to the first $\lfloor n/2 \rfloor$ parties is
maximally mixed. -/
def IsAME {n d : ℕ} (ψ : StateVector n d) : Prop :=
  IsNormalized ψ ∧
    ∀ π : Equiv.Perm (Fin n),
      HasMaximallyMixedFirstReduction (n := n) (d := d)
        (n / 2) (Nat.div_le_self n 2) (permuteState π ψ)


/-- An $\mathrm{AME}(n, d)$ state exists. -/
def ExistsAME (n d : ℕ) : Prop :=
  ∃ ψ : StateVector n d, IsAME (n := n) (d := d) ψ




/-- A configuration in which every party carries the same letter (vacuously true for
$n = 0$). -/
def IsConstantConfig {n d : ℕ} (x : Config n d) : Prop :=
  ∀ i j, x i = x j

/-- Being a constant configuration is decidable. -/
instance {n d : ℕ} : DecidablePred (@IsConstantConfig n d) := by
  intro x
  unfold IsConstantConfig
  infer_instance















/-! ## B. The `ZMod 5` circulant graph on ten vertices and its cuts -/

/-- The weighted circulant graph on `Fin 10` over `ZMod 5`: vertices at cyclic distance
$1$ get weight $3$, vertices at cyclic distance $2$ or $3$ get weight $1$, and all other
pairs get weight $0$. -/
def q5Graph (i j : Fin 10) : ZMod 5 :=
  let e := Nat.dist i.1 j.1
  let e := min e (10 - e)
  if e = 1 then 3 else if e = 2 ∨ e = 3 then 1 else 0



/-- The `5 × 5` cut matrix of `q5Graph` for a five-element set `A` of vertices: rows indexed
by the complement of `A`, columns by `A`, both in increasing order, so that the zero-based
entry `(i, j)` is the weight between the `i`-th vertex outside `A` and the `j`-th vertex of
`A`. -/
def q5CutMatrix (A : Finset (Fin 10)) (hA : A.card = 5) :
    Matrix (Fin 5) (Fin 5) (ZMod 5) :=
  let hAc : Aᶜ.card = 5 := by simp [Finset.card_compl, hA]
  fun i j => q5Graph ((Aᶜ.orderIsoOfFin hAc) i).1 ((A.orderIsoOfFin hA) j).1


/-- The vertices whose mask value is `b`, in increasing order; the list has between `0` and
`10` entries, depending on the mask. -/
def q5Indices (mask : Fin 10 → Bool) (b : Bool) : List (Fin 10) :=
  (List.finRange 10).filter (fun i => mask i == b)

/-- For `k : Fin 5`, the `k`-th vertex (zero-based, as a natural number) whose mask value is
`b`, or the fallback vertex `0` when fewer than `k + 1` vertices have mask value `b`. -/
def q5Select (mask : Fin 10 → Bool) (b : Bool) (k : Fin 5) : ℕ :=
  ((q5Indices mask b)[k.1]?.getD 0).1

/-- The weights of `q5Graph` as natural numbers, indexed by natural numbers; used to lift a
cut matrix to `ℤ` so that its determinant can be evaluated by the kernel. It uses the
truncated subtraction `10 - e` of `ℕ`. Its cast to `ZMod 5` agrees with `q5Graph` on
natural representatives `i j < 10`; outside that range it need not, for example
`q5GraphNat 0 11 = 0`, not the weight `3` of `(0, 1)`. -/
def q5GraphNat (i j : ℕ) : ℕ :=
  let e := Nat.dist i j
  let e := min e (10 - e)
  if e = 1 then 3 else if e = 2 ∨ e = 3 then 1 else 0

/-- The integer matrix attached to a Boolean mask on the ten vertices: the zero-based entry
`(i, j)` is `q5GraphNat` of the `i`-th `false` vertex and the `j`-th `true` vertex, as
chosen by `q5Select`. Any mask is accepted. Only for a mask with exactly five `true` entries
is this a cut matrix (it then lifts `q5CutMatrix` of the `true` set); otherwise missing rows
or columns use the fallback vertex `0`, and vertices past the fifth are dropped. -/
def q5MaskMatrix (mask : Fin 10 → Bool) : Matrix (Fin 5) (Fin 5) ℤ :=
  fun i j => q5GraphNat (q5Select mask false i) (q5Select mask true j)

set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma q5Indices_mem_sort (A : Finset (Fin 10)) :
    q5Indices (fun i => decide (i ∈ A)) true = A.sort (· ≤ ·) := by
  apply List.SortedLT.eq_of_mem_iff
  · exact ((List.sortedLT_finRange 10).pairwise.filter _).sortedLT
  · exact Finset.sortedLT_sort A
  · intro i
    simp [q5Indices]

lemma q5Indices_not_sort (A : Finset (Fin 10)) :
    q5Indices (fun i => decide (i ∈ A)) false = Aᶜ.sort (· ≤ ·) := by
  apply List.SortedLT.eq_of_mem_iff
  · exact ((List.sortedLT_finRange 10).pairwise.filter _).sortedLT
  · exact Finset.sortedLT_sort Aᶜ
  · intro i
    simp [q5Indices]

lemma q5Select_mem (A : Finset (Fin 10)) (hA : A.card = 5) (k : Fin 5) :
    q5Select (fun i => decide (i ∈ A)) true k = ((A.orderIsoOfFin hA) k).1.1 := by
  simp only [q5Select, q5Indices_mem_sort A]
  rw [List.getElem?_eq_getElem (by simpa [hA] using k.2)]
  rfl

set_option maxHeartbeats 0 in
lemma q5Select_not_mem (A : Finset (Fin 10)) (hA : A.card = 5) (k : Fin 5) :
    q5Select (fun i => decide (i ∈ A)) false k =
      ((Aᶜ.orderIsoOfFin (by simp [Finset.card_compl, hA])) k).1.1 := by
  simp only [q5Select, q5Indices_not_sort A]
  have hc : Aᶜ.card = 5 := by simp [Finset.card_compl, hA]
  rw [List.getElem?_eq_getElem (by simpa [hc] using k.2)]
  rfl

/-- The affine symmetries of the cycle `Fin 10`: a rotation by `s`, optionally preceded by
the reflection `i ↦ -i`, that is `i ↦ s + i` or (when `flip`) `i ↦ s - i`, modulo `10`.
They preserve `q5Graph` (`q5Graph_affine`). -/
def q5Affine (s : Fin 10) (flip : Bool) : Equiv.Perm (Fin 10) :=
  if flip then (Equiv.neg (Fin 10)).trans (Equiv.addLeft s) else Equiv.addLeft s

lemma q5Graph_affine (s : Fin 10) (flip : Bool) (i j : Fin 10) :
    q5Graph (q5Affine s flip i) (q5Affine s flip j) = q5Graph i j := by
  decide +revert


/-- Representatives of the orbits of the five-element subsets of `Fin 10` under the affine
symmetries `q5Affine`. -/
def q5Representatives : List (Finset (Fin 10)) :=
  [ {0, 1, 2, 3, 4}, {0, 1, 2, 3, 5}, {0, 1, 2, 4, 5},
    {0, 1, 2, 3, 6}, {0, 1, 2, 4, 6}, {0, 1, 3, 4, 6},
    {0, 2, 3, 4, 6}, {0, 1, 2, 5, 6}, {0, 1, 3, 5, 6},
    {0, 1, 2, 4, 7}, {0, 1, 3, 4, 7}, {0, 1, 2, 5, 7},
    {0, 1, 3, 5, 7}, {0, 2, 3, 5, 7}, {0, 1, 4, 5, 7},
    {0, 2, 4, 6, 8} ]

lemma q5Representatives_card (R : Finset (Fin 10)) (hR : R ∈ q5Representatives) :
    R.card = 5 := by
  simp only [q5Representatives, List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

lemma q5Cut_classification (A : Finset (Fin 10)) (hA : A.card = 5) :
    ∃ R ∈ q5Representatives, ∃ s : Fin 10, ∃ flip : Bool,
      A = R.map (q5Affine s flip).toEmbedding := by
  set_option maxRecDepth 10000 in
    revert A
    exact of_decide_eq_true rfl



lemma q5Representative_certificate : ∀ R : Finset (Fin 10),
    R ∈ q5Representatives →
      detFinFiveInt (q5MaskMatrix (fun i => decide (i ∈ R))) % 5 ≠ 0 := by
  intro R hR
  simp only [q5Representatives, List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals exact of_decide_eq_true rfl

lemma q5CutMatrix_det_of_certificate (A : Finset (Fin 10)) (hA : A.card = 5)
    (hcert : detFinFiveInt
      (q5MaskMatrix (fun i => decide (i ∈ A))) % 5 ≠ 0) :
    (q5CutMatrix A hA).det ≠ 0 := by
  let mask : Fin 10 → Bool := fun i => decide (i ∈ A)
  let M : Matrix (Fin 5) (Fin 5) ℤ := q5MaskMatrix mask
  have hmap : (Int.castRingHom (ZMod 5)).mapMatrix M = q5CutMatrix A hA := by
    funext i j
    change ((q5GraphNat (q5Select (fun i => decide (i ∈ A)) false i)
      (q5Select (fun i => decide (i ∈ A)) true j) : ℤ) : ZMod 5) = _
    rw [q5Select_not_mem A hA i, q5Select_mem A hA j]
    simp only [q5CutMatrix, q5GraphNat, q5Graph]
    split_ifs <;> norm_num
  intro hz
  have hz' : ((M.det : ℤ) : ZMod 5) = 0 := by
    calc
      ((M.det : ℤ) : ZMod 5) =
          ((Int.castRingHom (ZMod 5)).mapMatrix M).det := Int.cast_det M
      _ = (q5CutMatrix A hA).det := congrArg Matrix.det hmap
      _ = 0 := hz
  have hdvd : (5 : ℤ) ∣ M.det :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (M.det) 5).mp hz'
  apply hcert
  change detFinFiveInt M % 5 = 0
  rw [← detFinFiveInt_eq M]
  exact Int.emod_eq_zero_of_dvd hdvd

lemma q5CutMatrix_det_map (A : Finset (Fin 10)) (hA : A.card = 5)
    (g : Equiv.Perm (Fin 10))
    (hg : ∀ i j, q5Graph (g i) (g j) = q5Graph i j)
    (hd : (q5CutMatrix A hA).det ≠ 0) :
    (q5CutMatrix (A.map g.toEmbedding) (by simpa using hA)).det ≠ 0 := by
  let B := A.map g.toEmbedding
  let hB : B.card = 5 := by simpa [B] using hA
  let hAc : Aᶜ.card = 5 := by simp [Finset.card_compl, hA]
  let hBc : Bᶜ.card = 5 := by simp [Finset.card_compl, hB]
  let eA := A.orderIsoOfFin hA
  let eB := B.orderIsoOfFin hB
  let eC := Aᶜ.orderIsoOfFin hAc
  let eD := Bᶜ.orderIsoOfFin hBc
  let mapA := Finset.equivMap g.toEmbedding A
  let pA : Equiv.Perm (Fin 5) :=
    eA.toEquiv.trans (mapA.trans eB.toEquiv.symm)
  let pC : Equiv.Perm (Fin 5) :=
    eC.toEquiv.trans ((finsetMapComplEquiv g A).trans eD.toEquiv.symm)
  have hmat : q5CutMatrix A hA =
      (q5CutMatrix B hB).submatrix pC pA := by
    ext i j
    show q5Graph (eC i).1 (eA j).1 = q5Graph (eD (pC i)).1 (eB (pA j)).1
    have hpA : (eB (pA j)).1 = g (eA j).1 := by
      change (eB (eB.symm (mapA (eA j)))).1 = (mapA (eA j)).1
      exact congrArg Subtype.val (eB.apply_symm_apply (mapA (eA j)))
    have hpC : (eD (pC i)).1 = g (eC i).1 := by
      change (eD (eD.symm ((finsetMapComplEquiv g A) (eC i)))).1 =
        ((finsetMapComplEquiv g A) (eC i)).1
      exact congrArg Subtype.val (eD.apply_symm_apply ((finsetMapComplEquiv g A) (eC i)))
    rw [hpA, hpC]
    exact (hg _ _).symm
  intro hz
  have hzB : (q5CutMatrix B hB).det = 0 := by
    simpa [B] using hz
  apply hd
  rw [hmat]
  have hdet := Matrix.det_reindex pC.symm pA.symm (q5CutMatrix B hB)
  rw [Matrix.reindex_apply] at hdet
  simpa [hzB] using hdet


lemma q5CutMatrix_det (A : Finset (Fin 10)) (hA : A.card = 5) :
    (q5CutMatrix A hA).det ≠ 0 := by
  obtain ⟨R, hR, s, flip, rfl⟩ := q5Cut_classification A hA
  have hRc := q5Representatives_card R hR
  apply q5CutMatrix_det_map R hRc (q5Affine s flip) (q5Graph_affine s flip)
  exact q5CutMatrix_det_of_certificate R hRc (q5Representative_certificate R hR)


lemma q5Graph_cut_injective (A : Finset (Fin 10)) (hA : A.card = 5) :
    Function.Injective (fun x : A → ZMod 5 =>
      fun j : {j : Fin 10 // j ∉ A} =>
        ∑ i : A, q5Graph j.1 i.1 * x i) := by
  intro x y hxy
  let hAc : Aᶜ.card = 5 := by simp [Finset.card_compl, hA]
  let eA := A.orderIsoOfFin hA
  let eC := Aᶜ.orderIsoOfFin hAc
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hd : IsUnit (q5CutMatrix A hA).det :=
    (isUnit_iff_ne_zero).2 (q5CutMatrix_det A hA)
  have hu : IsUnit (q5CutMatrix A hA) :=
    (Matrix.isUnit_iff_isUnit_det _).2 hd
  have hvout : (q5CutMatrix A hA).mulVec (x ∘ eA) =
      (q5CutMatrix A hA).mulVec (y ∘ eA) := by
    funext r
    have her : (eC r).1 ∉ A := by
      simpa only [Finset.mem_compl] using (eC r).2
    have hr := congrFun hxy ⟨(eC r).1, her⟩
    change (∑ j : Fin 5, q5Graph (eC r).1 (eA j).1 * x (eA j)) =
      ∑ j : Fin 5, q5Graph (eC r).1 (eA j).1 * y (eA j)
    calc
      _ = ∑ i : A, q5Graph (eC r).1 i.1 * x i :=
        eA.toEquiv.sum_comp (fun i : A => q5Graph (eC r).1 i.1 * x i)
      _ = ∑ i : A, q5Graph (eC r).1 i.1 * y i := hr
      _ = _ := (eA.toEquiv.sum_comp
        (fun i : A => q5Graph (eC r).1 i.1 * y i)).symm
  have hv := Matrix.mulVec_injective_of_isUnit hu hvout
  funext i
  obtain ⟨r, rfl⟩ := eA.surjective i
  exact congrFun hv r


/-! ## C. The `ZMod 2` nine-cycle graph and its code -/

/-- The adjacency function over `ZMod 2` of the nine-cycle on `Fin 9`. -/
def q2Cycle (i j : Fin 9) : ZMod 2 :=
  if Nat.dist i.1 j.1 = 1 ∨ Nat.dist i.1 j.1 = 8 then 1 else 0

lemma q2Cycle_symm (i j : Fin 9) : q2Cycle i j = q2Cycle j i := by
  simp only [q2Cycle, Nat.dist_comm]

lemma q2Cycle_diag (i : Fin 9) : q2Cycle i i = 0 := by
  simp [q2Cycle]

lemma q5Graph_symm (i j : Fin 10) : q5Graph i j = q5Graph j i := by
  simp only [q5Graph, Nat.dist_comm]

lemma q5Graph_diag (i : Fin 10) : q5Graph i i = 0 := by
  simp [q5Graph]



lemma graph_cross_generic {n p : ℕ} (G : Fin n → Fin n → ZMod p)
    (hsym : ∀ i j, G i j = G j i) (hdiag : ∀ i, G i i = 0)
    (x d : Fin n → ZMod p) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.1 < j.1),
      G i j * (x i * d j + d i * x j)) =
      ∑ i, x i * ∑ j, G i j * d j := by
  calc
    _ = ∑ i, ∑ j ∈ Finset.Ioi i,
        ((x i * G i j * d j) + (x j * G j i * d i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr
      · ext j
        simp
      · intro j hj
        rw [← hsym i j]
        ring
    _ = ∑ i, ∑ j ∈ ({i}ᶜ : Finset (Fin n)), x i * G i j * d j :=
      Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      have he : Finset.univ.erase i = ({i}ᶜ : Finset (Fin n)) := by
        ext j
        simp [eq_comm]
      have hs := Finset.sum_erase_add Finset.univ
        (fun j => x i * (G i j * d j)) (Finset.mem_univ i)
      rw [he] at hs
      rw [← hs]
      simp [hdiag]
      apply Finset.sum_congr rfl
      intro j hj
      ring

lemma q2Cycle_cross (x d : Fin 9 → ZMod 2) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin 9 => i.1 < j.1),
      q2Cycle i j * (x i * d j + d i * x j)) =
      ∑ i, x i * ∑ j, q2Cycle i j * d j :=
  graph_cross_generic q2Cycle q2Cycle_symm q2Cycle_diag x d

lemma q5Graph_cross (x d : Fin 10 → ZMod 5) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin 10 => i.1 < j.1),
      q5Graph i j * (x i * d j + d i * x j)) =
      ∑ i, x i * ∑ j, q5Graph i j * d j :=
  graph_cross_generic q5Graph q5Graph_symm q5Graph_diag x d


/-- The first parity check of the `ZMod 2` code: the sum of the coordinates
$0, 1, 3, 4, 6, 7$. -/
def q2Check₁ (x : Fin 9 → ZMod 2) : ZMod 2 :=
  x 0 + x 1 + x 3 + x 4 + x 6 + x 7

/-- The second parity check of the `ZMod 2` code: the sum of the coordinates
$0, 2, 3, 5, 6, 8$. -/
def q2Check₂ (x : Fin 9 → ZMod 2) : ZMod 2 :=
  x 0 + x 2 + x 3 + x 5 + x 6 + x 8



lemma q2Cycle_subgroup_minWeight (x : Fin 9 → ZMod 2)
    (h1 : q2Check₁ x = 0) (h2 : q2Check₂ x = 0) (hx : x ≠ 0) :
    5 ≤ (Finset.univ.filter fun i =>
      x i ≠ 0 ∨ (∑ j, q2Cycle i j * x j) ≠ 0).card := by
  set_option maxRecDepth 10000 in
    decide +revert



/-! ## D. Characters, local splitting, and graph phases -/

/-- The factorisation `Fin 2 × Fin 5 ≃ Fin 10` of a single party's local dimension. -/
def localTenEquiv : Fin 2 × Fin 5 ≃ Fin 10 := finProdFinEquiv

/-- The qubit part of a local letter. -/
def bitPart (x : Fin 10) : ZMod 2 := (localTenEquiv.symm x).1

/-- The qudit (`ZMod 5`) part of a local letter. -/
def quintPart (x : Fin 10) : ZMod 5 := (localTenEquiv.symm x).2


/-- A local letter is the same thing as a pair consisting of a `ZMod 2` letter and a
`ZMod 5` letter: `x ↦ (bitPart x, quintPart x)`. -/
def localPartsEquiv : Fin 10 ≃ ZMod 2 × ZMod 5 :=
  localTenEquiv.symm.trans
    (Equiv.prodCongr (ZMod.finEquiv 2).toEquiv (ZMod.finEquiv 5).toEquiv)

@[simp] lemma localPartsEquiv_apply (x : Fin 10) :
    localPartsEquiv x = (bitPart x, quintPart x) := rfl



/-- The quadratic phase $\sum_{i < j} G_{ij} x_i x_j$ of a graph state with weight matrix
`G` over `ZMod p`. -/
def graphPhase {n p : ℕ} (G : Fin n → Fin n → ZMod p)
    (x : Fin n → ZMod p) : ZMod p :=
  ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.1 < j.1),
    G i j * x i * x j

lemma graphPhase_add {n p : ℕ} (G : Fin n → Fin n → ZMod p)
    (x d : Fin n → ZMod p) :
    graphPhase G (x + d) = graphPhase G x + graphPhase G d +
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.1 < j.1),
        G i j * (x i * d j + d i * x j) := by
  simp only [graphPhase, Pi.add_apply]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  simp only [mul_comm, mul_assoc, mul_left_comm]
  ring

lemma q2Phase_sub (x y : Fin 9 → ZMod 2) :
    graphPhase q2Cycle x - graphPhase q2Cycle y =
      graphPhase q2Cycle (x - y) +
        ∑ i, y i * ∑ j, q2Cycle i j * (x j - y j) := by
  have h := graphPhase_add q2Cycle y (x - y)
  rw [show y + (x - y) = x by abel] at h
  rw [h, q2Cycle_cross]
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

lemma q5Phase_sub (x y : Fin 10 → ZMod 5) :
    graphPhase q5Graph x - graphPhase q5Graph y =
      graphPhase q5Graph (x - y) +
        ∑ i, y i * ∑ j, q5Graph i j * (x j - y j) := by
  have h := graphPhase_add q5Graph y (x - y)
  rw [show y + (x - y) = x by abel] at h
  rw [h, q5Graph_cross]
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

/-- The `ZMod 2` logical label attached to the logical qubits `a`: the linear combination,
with coefficients `a 0` and `a 1`, of the check vectors of `q2Check₁` and `q2Check₂` (the
indicator vectors of the coordinates $\{0, 1, 3, 4, 6, 7\}$ and $\{0, 2, 3, 5, 6, 8\}$). -/
def q2Label (a : Fin 2 → ZMod 2) (i : Fin 9) : ZMod 2 :=
  a 0 * (if i.1 ∈ ([0, 1, 3, 4, 6, 7] : List ℕ) then 1 else 0) +
  a 1 * (if i.1 ∈ ([0, 2, 3, 5, 6, 8] : List ℕ) then 1 else 0)

set_option maxRecDepth 10000 in
lemma q2Label_dot (a : Fin 2 → ZMod 2) (x : Fin 9 → ZMod 2) :
    (∑ i, q2Label a i * x i) =
      a 0 * q2Check₁ x + a 1 * q2Check₂ x := by
  decide +revert

/-- The `ZMod 5` letter carried by the logical qubits `a`: both bits are lifted to their
natural representatives in $\{0, 1\}$ (`ZMod.val`), and $a_0 + 2 a_1 \in \{0, 1, 2, 3\}$ is
computed in `ℕ` and cast to `ZMod 5`. -/
def q5Logical (a : Fin 2 → ZMod 2) : ZMod 5 :=
  ((a 0).val + 2 * (a 1).val : ℕ)

/-- The `ZMod 2` phase of the state: the nine-cycle graph phase of the qubit word `u`, plus
its dot product $\sum_i (\mathrm{q2Label}\ a)_i u_i$ with the logical label. -/
def binaryPhase (a : Fin 2 → ZMod 2) (u : Fin 9 → ZMod 2) : ZMod 2 :=
  graphPhase q2Cycle u + ∑ i, q2Label a i * u i

/-- The ten-letter `ZMod 5` word obtained from the nine physical letters `v` by inserting the
logical letter `q5Logical a` in position `0`. -/
def quinaryWord (a : Fin 2 → ZMod 2) (v : Fin 9 → ZMod 5) : Fin 10 → ZMod 5
  | ⟨0, _⟩ => q5Logical a
  | ⟨i + 1, h⟩ => v ⟨i, by omega⟩

@[simp] lemma quinaryWord_zero (a : Fin 2 → ZMod 2) (v : Fin 9 → ZMod 5) :
    quinaryWord a v 0 = q5Logical a := rfl

@[simp] lemma quinaryWord_succ (a : Fin 2 → ZMod 2) (v : Fin 9 → ZMod 5)
    (i : Fin 9) : quinaryWord a v (Fin.succ i) = v i := by
  rfl

/-- The `ZMod 5` phase of the state: the circulant graph phase of the ten-letter word. -/
def quinaryPhase (a : Fin 2 → ZMod 2) (v : Fin 9 → ZMod 5) : ZMod 5 :=
  graphPhase q5Graph (quinaryWord a v)

/-! ## E. The state and its normalisation -/

/-- The amplitude of the constructed state on a computational-basis configuration: the
uniform superposition over the two logical qubits of the product of the two graph-state
phases, multiplied by $(2^{11} 5^9)^{-1/2}$. Here the qubit word `u` and the qudit word
`v` are the `bitPart` and `quintPart` of the letters of `x`, and the phases enter through
`ZMod.stdAddChar`. -/
noncomputable def ameAmplitude (x : Config 9 10) : ℂ :=
  let u : Fin 9 → ZMod 2 := fun i => bitPart (x i)
  let v : Fin 9 → ZMod 5 := fun i => quintPart (x i)
  ((Real.sqrt (2 ^ 11 * 5 ^ 9 : ℝ) : ℂ)⁻¹) *
    ∑ a : Fin 2 → ZMod 2,
      ZMod.stdAddChar (binaryPhase a u) * ZMod.stdAddChar (quinaryPhase a v)

/-- The candidate $\mathrm{AME}(9, 10)$ state: the vector with amplitudes `ameAmplitude`. -/
noncomputable def ameState : StateVector 9 10 := mkStateVector ameAmplitude

/-- The assertion that an $\mathrm{AME}(9, 10)$ state exists, named so that the proof can be
stated against it. -/
def ame_9_10_open_statement : Prop := ExistsAME 9 10

lemma q5Graph_zero_of_supported (A : Finset (Fin 10)) (hA : A.card = 5)
    (d : Fin 10 → ZMod 5) (hsupp : ∀ i, i ∉ A → d i = 0)
    (hcoeff : ∀ j, j ∉ A → (∑ i, q5Graph j i * d i) = 0) : d = 0 := by
  have hxy : (fun j : {j : Fin 10 // j ∉ A} =>
        ∑ i : A, q5Graph j.1 i.1 * d i.1) =
      (fun _ : {j : Fin 10 // j ∉ A} => 0) := by
    funext j
    rw [← hcoeff j.1 j.2]
    calc
      (∑ i : A, q5Graph j.1 i.1 * d i.1) =
          ∑ i ∈ A, q5Graph j.1 i * d i := by
            simpa only [] using
              (Finset.sum_coe_sort A (fun i : Fin 10 => q5Graph j.1 i * d i))
      _ = ∑ i, q5Graph j.1 i * d i := by
        apply Finset.sum_subset (Finset.subset_univ A)
        intro i _ hi
        rw [hsupp i hi, mul_zero]
  have hdA : (fun i : A => d i.1) = 0 := by
    apply q5Graph_cut_injective A hA
    simpa using hxy
  funext i
  by_cases hi : i ∈ A
  · exact congrFun hdA ⟨i, hi⟩
  · exact hsupp i hi

lemma q2Cycle_zero_of_small_supported (A : Finset (Fin 9)) (hA : A.card ≤ 4)
    (d : Fin 9 → ZMod 2) (hsupp : ∀ i, i ∉ A → d i = 0)
    (hcoeff : ∀ j, j ∉ A → (∑ i, q2Cycle j i * d i) = 0)
    (h1 : q2Check₁ d = 0) (h2 : q2Check₂ d = 0) : d = 0 := by
  by_contra hd
  have hw := q2Cycle_subgroup_minWeight d h1 h2 hd
  let B := Finset.univ.filter fun i =>
    d i ≠ 0 ∨ (∑ j, q2Cycle i j * d j) ≠ 0
  have hBA : B ⊆ A := by
    intro i hi
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_contra hn
    exact hi.elim (fun h => h (hsupp i hn)) (fun h => h (hcoeff i hn))
  change 5 ≤ B.card at hw
  have hcard : B.card ≤ A.card := Finset.card_le_card hBA
  omega

set_option maxHeartbeats 0

lemma q2_phase_paste_affine (A : Finset (Fin 9)) (a : Fin 2 → ZMod 2)
    (x y : A → ZMod 2) (z : {i : Fin 9 // i ∉ A} → ZMod 2) :
    let d := pasteOn A x 0 - pasteOn A y 0
    binaryPhase a (pasteOn A x z) - binaryPhase a (pasteOn A y z) =
      (graphPhase q2Cycle d +
        ∑ i ∈ A.attach, y i * ∑ j, q2Cycle i.1 j * d j +
        ∑ i, q2Label a i * d i) +
        ∑ i : {i : Fin 9 // i ∉ A},
          z i * (∑ j, q2Cycle i.1 j * d j) := by
  dsimp only
  have hd : pasteOn A x z - pasteOn A y z =
      pasteOn A x 0 - pasteOn A y 0 := by
    funext i
    by_cases hi : i ∈ A <;> simp [pasteOn, hi]
  have hg := q2Phase_sub (pasteOn A x z) (pasteOn A y z)
  simp only [binaryPhase]
  rw [show
    (graphPhase q2Cycle (pasteOn A x z) +
        ∑ i, q2Label a i * pasteOn A x z i) -
      (graphPhase q2Cycle (pasteOn A y z) +
        ∑ i, q2Label a i * pasteOn A y z i) =
      (graphPhase q2Cycle (pasteOn A x z) -
        graphPhase q2Cycle (pasteOn A y z)) +
      ((∑ i, q2Label a i * pasteOn A x z i) -
        ∑ i, q2Label a i * pasteOn A y z i) by ring]
  rw [hg, hd]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← mul_sub]
  have hdj (j : Fin 9) : pasteOn A x z j - pasteOn A y z j =
      (pasteOn A x 0 - pasteOn A y 0) j := congrFun hd j
  simp_rw [hdj]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin 9 => i ∈ A)
    (fun i => pasteOn A y z i *
      ∑ j, q2Cycle i j * (pasteOn A x 0 - pasteOn A y 0) j)]
  simp only [pasteOn_mem, pasteOn_not_mem]
  rw [add_assoc]
  have hu : (@Finset.univ {i : Fin 9 // i ∈ A} (Subtype.fintype _)) =
      (@Finset.univ (↥A) (Finset.Subtype.fintype A)) := by
    ext i
    simp
  rw [hu]
  rw [Finset.sum_coe_sort_eq_attach A]
  ring

lemma sum_binary_labels (b : ZMod 2) (d : Fin 9 → ZMod 2) :
    (∑ a : Fin 2 → ZMod 2,
      ZMod.stdAddChar (b + ∑ i, q2Label a i * d i)) =
      if q2Check₁ d = 0 ∧ q2Check₂ d = 0 then
        (4 : ℂ) * ZMod.stdAddChar b else 0 := by
  let c : Fin 2 → ZMod 2 := ![q2Check₁ d, q2Check₂ d]
  have hdot (a : Fin 2 → ZMod 2) :
      (∑ i, q2Label a i * d i) = ∑ k, c k * a k := by
    rw [q2Label_dot]
    simp only [c, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  simp_rw [hdot]
  rw [sum_stdAddChar_affine]
  have hc : c = 0 ↔ q2Check₁ d = 0 ∧ q2Check₂ d = 0 := by
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h1, h2⟩
      funext i
      fin_cases i <;> simp [c, h1, h2]
  by_cases h : c = 0
  · have hh := hc.mp h
    simp [h, hh]
    ring
  · have hh : ¬(q2Check₁ d = 0 ∧ q2Check₂ d = 0) := fun hh => h (hc.mpr hh)
    simp [h, hh]

lemma q2_phase_paste_sum (A : Finset (Fin 9)) (hA : A.card = 4)
    (x y : A → ZMod 2) :
    (∑ a : Fin 2 → ZMod 2,
      ∑ z : {i : Fin 9 // i ∉ A} → ZMod 2,
        ZMod.stdAddChar (binaryPhase a (pasteOn A x z)) *
          star (ZMod.stdAddChar (binaryPhase a (pasteOn A y z)))) =
      if x = y then (2 ^ 7 : ℂ) else 0 := by
  let d : Fin 9 → ZMod 2 := pasteOn A x 0 - pasteOn A y 0
  let c : {i : Fin 9 // i ∉ A} → ZMod 2 :=
    fun i => ∑ j, q2Cycle i.1 j * d j
  let b : ZMod 2 := graphPhase q2Cycle d +
    ∑ i ∈ A.attach, y i * ∑ j, q2Cycle i.1 j * d j
  have hform (a : Fin 2 → ZMod 2) (z : {i : Fin 9 // i ∉ A} → ZMod 2) :
      binaryPhase a (pasteOn A x z) - binaryPhase a (pasteOn A y z) =
        (b + ∑ i, q2Label a i * d i) + ∑ i, c i * z i := by
    rw [q2_phase_paste_affine]
    dsimp [b, c, d]
    congr 2
    funext i
    ac_rfl
  simp_rw [stdAddChar_mul_star, hform, sum_stdAddChar_affine]
  have hcard : Fintype.card {i : Fin 9 // i ∉ A} = 5 := by
    rw [Fintype.card_subtype_compl (fun i : Fin 9 => i ∈ A)]
    simpa [hA] using (show Fintype.card (Fin 9) - A.card = 5 by simp [hA])
  by_cases hc : c = 0
  · rw [if_pos hc]
    simp only [hcard]
    rw [← Finset.sum_mul, sum_binary_labels]
    by_cases hh : q2Check₁ d = 0 ∧ q2Check₂ d = 0
    · have hd : d = 0 := by
        apply q2Cycle_zero_of_small_supported A (by omega)
        · intro i hi
          simp [d, pasteOn, hi]
        · intro i hi
          exact congrFun hc ⟨i, hi⟩
        · exact hh.1
        · exact hh.2
      have hxy : x = y := by
        funext i
        have hi := congrFun hd i.1
        exact sub_eq_zero.mp (by simpa [d, pasteOn, i.2] using hi)
      subst y
      have hh0 : q2Check₁ (0 : Fin 9 → ZMod 2) = 0 ∧
          q2Check₂ (0 : Fin 9 → ZMod 2) = 0 := by
        simp [q2Check₁, q2Check₂]
      simp [hd, b, hh0, graphPhase]
      norm_num
    · have hxy : x ≠ y := by
        intro hxy
        subst y
        apply hh
        constructor <;> simp [d, q2Check₁, q2Check₂]
      simp [hh, hxy]
  · have hxy : x ≠ y := by
      intro hxy
      subst y
      apply hc
      funext i
      simp [c, d]
    simp [hc, hxy]

/-- Add the logical vertex `0` to a set of physical vertices, each physical vertex `i` being
shifted to `i + 1` in `Fin 10`. -/
def liftPhysicalSet (A : Finset (Fin 9)) : Finset (Fin 10) :=
  {0} ∪ A.map ⟨Fin.succ, Fin.succ_injective 9⟩

@[simp] lemma liftPhysicalSet_card (A : Finset (Fin 9)) :
    (liftPhysicalSet A).card = A.card + 1 := by
  rw [liftPhysicalSet, Finset.card_union_of_disjoint]
  · simp
    omega
  · simp [Finset.disjoint_left]

@[simp] lemma liftPhysicalSet_zero (A : Finset (Fin 9)) :
    (0 : Fin 10) ∈ liftPhysicalSet A := by simp [liftPhysicalSet]

@[simp] lemma liftPhysicalSet_succ (A : Finset (Fin 9)) (i : Fin 9) :
    Fin.succ i ∈ liftPhysicalSet A ↔ i ∈ A := by
  simp [liftPhysicalSet]

lemma q5Logical_injective : Function.Injective q5Logical := by
  decide +revert

lemma quinary_phase_physical_sum (A : Finset (Fin 9)) (hA : A.card = 4)
    (a b : Fin 2 → ZMod 2) (x y : A → ZMod 5) :
    (∑ z : {i : Fin 9 // i ∉ A} → ZMod 5,
      ZMod.stdAddChar (quinaryPhase a (pasteOn A x z)) *
        star (ZMod.stdAddChar (quinaryPhase b (pasteOn A y z)))) =
      if a = b ∧ x = y then (5 ^ 5 : ℂ) else 0 := by
  let d : Fin 10 → ZMod 5 :=
    quinaryWord a (pasteOn A x 0) - quinaryWord b (pasteOn A y 0)
  let c : {i : Fin 9 // i ∉ A} → ZMod 5 :=
    fun i => ∑ j, q5Graph (Fin.succ i.1) j * d j
  let e : ZMod 5 := graphPhase q5Graph d +
    q5Logical b * (∑ j, q5Graph 0 j * d j) +
    ∑ i ∈ A.attach, y i * ∑ j, q5Graph (Fin.succ i.1) j * d j
  have hd (z : {i : Fin 9 // i ∉ A} → ZMod 5) :
      quinaryWord a (pasteOn A x z) - quinaryWord b (pasteOn A y z) = d := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [d]
    · by_cases hk : k ∈ A <;> simp [d, pasteOn, hk]
  have hform (z : {i : Fin 9 // i ∉ A} → ZMod 5) :
      quinaryPhase a (pasteOn A x z) - quinaryPhase b (pasteOn A y z) =
        e + ∑ i, c i * z i := by
    unfold quinaryPhase
    rw [q5Phase_sub]
    have hdj (j : Fin 10) :
        quinaryWord a (pasteOn A x z) j - quinaryWord b (pasteOn A y z) j = d j :=
      congrFun (hd z) j
    simp_rw [hdj]
    have hsplit :
        (∑ i : Fin 10, quinaryWord b (pasteOn A y z) i *
          ∑ j, q5Graph i j * d j) =
        q5Logical b * (∑ j, q5Graph 0 j * d j) +
          ∑ i : Fin 9, pasteOn A y z i *
            ∑ j, q5Graph (Fin.succ i) j * d j := by
      rw [Fin.sum_univ_succ]
      simp only [quinaryWord_zero, quinaryWord_succ]
    rw [hsplit]
    have hparts :
        (∑ i : Fin 9, pasteOn A y z i *
          ∑ j, q5Graph (Fin.succ i) j * d j) =
        (∑ i ∈ A.attach, y i * ∑ j, q5Graph (Fin.succ i.1) j * d j) +
          ∑ i : {i : Fin 9 // i ∉ A}, z i *
            ∑ j, q5Graph (Fin.succ i.1) j * d j := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin 9 => i ∈ A)]
      simp only [pasteOn_mem, pasteOn_not_mem]
      have hu : (@Finset.univ {i : Fin 9 // i ∈ A} (Subtype.fintype _)) =
          (@Finset.univ (↥A) (Finset.Subtype.fintype A)) := by
        ext i
        simp
      rw [hu, Finset.sum_coe_sort_eq_attach A]
    have hg := congrArg (graphPhase q5Graph) (hd z)
    rw [hg]
    rw [hparts]
    dsimp only [e, c]
    have ht :
        (∑ i : {i : Fin 9 // i ∉ A}, z i *
          ∑ j, q5Graph (Fin.succ i.1) j * d j) =
        ∑ i : {i : Fin 9 // i ∉ A},
          (∑ j, q5Graph (Fin.succ i.1) j * d j) * z i := by
      apply Finset.sum_congr rfl
      intro i hi
      ac_rfl
    rw [ht]
    ring
  simp_rw [stdAddChar_mul_star, hform, sum_stdAddChar_affine]
  have hcard : Fintype.card {i : Fin 9 // i ∉ A} = 5 := by
    rw [Fintype.card_subtype_compl (fun i : Fin 9 => i ∈ A)]
    simpa [hA] using (show Fintype.card (Fin 9) - A.card = 5 by simp [hA])
  have hc : c = 0 ↔ a = b ∧ x = y := by
    constructor
    · intro hc0
      have hd0 : d = 0 := by
        apply q5Graph_zero_of_supported (liftPhysicalSet A) (by simp [hA])
        · intro i hi
          have hi0 : i ≠ 0 := by
            intro hiEq
            subst i
            exact hi (liftPhysicalSet_zero A)
          obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hi0
          have hk : k ∉ A := by simpa using hi
          simp [d, pasteOn, hk]
        · intro i hi
          have hi0 : i ≠ 0 := by
            intro hiEq
            subst i
            exact hi (liftPhysicalSet_zero A)
          obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hi0
          have hk : k ∉ A := by simpa using hi
          exact congrFun hc0 ⟨k, hk⟩
      constructor
      · apply q5Logical_injective
        have hz := congrFun hd0 0
        exact sub_eq_zero.mp (by simpa [d] using hz)
      · funext i
        have hi := congrFun hd0 (Fin.succ i.1)
        exact sub_eq_zero.mp (by simpa [d, pasteOn, i.2] using hi)
    · rintro ⟨rfl, rfl⟩
      funext i
      simp [c, d]
  by_cases h : a = b ∧ x = y
  · have hc0 := hc.mpr h
    rw [if_pos hc0, if_pos h]
    simp only [hcard]
    rcases h with ⟨rfl, rfl⟩
    have hd0 : d = 0 := by
      funext i
      simp [d]
    simp [hd0, e, graphPhase]
  · have hc0 : c ≠ 0 := fun hc0 => h (hc.mp hc0)
    simp [hc0, h]

lemma q5_phase_paste_affine (A : Finset (Fin 10))
    (x y : A → ZMod 5) (z : {i : Fin 10 // i ∉ A} → ZMod 5) :
    let d := pasteOn A x 0 - pasteOn A y 0
    graphPhase q5Graph (pasteOn A x z) - graphPhase q5Graph (pasteOn A y z) =
      (graphPhase q5Graph d +
        ∑ i ∈ A.attach, y i * ∑ j, q5Graph i.1 j * d j) +
        ∑ i : {i : Fin 10 // i ∉ A},
          z i * (∑ j, q5Graph i.1 j * d j) := by
  dsimp only
  have hd : pasteOn A x z - pasteOn A y z =
      pasteOn A x 0 - pasteOn A y 0 := by
    funext i
    by_cases hi : i ∈ A
    · simp [pasteOn, hi]
    · simp [pasteOn, hi]
  rw [q5Phase_sub, hd]
  have hdj (j : Fin 10) : pasteOn A x z j - pasteOn A y z j =
      (pasteOn A x 0 - pasteOn A y 0) j := congrFun hd j
  simp_rw [hdj]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin 10 => i ∈ A)
    (fun i => pasteOn A y z i *
      ∑ j, q5Graph i j * (pasteOn A x 0 - pasteOn A y 0) j)]
  simp only [pasteOn_mem, pasteOn_not_mem]
  rw [add_assoc]
  congr 2
  have hu : (@Finset.univ {i : Fin 10 // i ∈ A} (Subtype.fintype _)) =
      (@Finset.univ (↥A) (Finset.Subtype.fintype A)) := by
    ext i
    simp
  rw [hu]
  exact (Finset.sum_coe_sort_eq_attach A
    (fun i : A => y i * ∑ j, q5Graph i.1 j *
      (pasteOn A x 0 - pasteOn A y 0) j))

lemma q5_phase_paste_sum (A : Finset (Fin 10)) (hA : A.card = 5)
    (x y : A → ZMod 5) :
    (∑ z : {i : Fin 10 // i ∉ A} → ZMod 5,
      ZMod.stdAddChar (graphPhase q5Graph (pasteOn A x z)) *
        star (ZMod.stdAddChar (graphPhase q5Graph (pasteOn A y z)))) =
      if x = y then (5 ^ 5 : ℂ) else 0 := by
  let d : Fin 10 → ZMod 5 := pasteOn A x 0 - pasteOn A y 0
  let c : {i : Fin 10 // i ∉ A} → ZMod 5 :=
    fun i => ∑ j, q5Graph i.1 j * d j
  let b : ZMod 5 := graphPhase q5Graph d +
    ∑ i ∈ A.attach, y i * ∑ j, q5Graph i.1 j * d j
  have hform (z : {i : Fin 10 // i ∉ A} → ZMod 5) :
      graphPhase q5Graph (pasteOn A x z) - graphPhase q5Graph (pasteOn A y z) =
        b + ∑ i, c i * z i := by
    rw [q5_phase_paste_affine]
    dsimp [b, c, d]
    congr 2
    funext i
    ac_rfl
  simp_rw [stdAddChar_mul_star, hform]
  rw [sum_stdAddChar_affine]
  have hc : c = 0 ↔ x = y := by
    constructor
    · intro hc
      have hd : d = 0 := by
        apply q5Graph_zero_of_supported A hA
        · intro i hi
          simp [d, pasteOn, hi]
        · intro i hi
          exact congrFun hc ⟨i, hi⟩
      funext i
      have hi := congrFun hd i.1
      exact sub_eq_zero.mp (by simpa [d, pasteOn, i.2] using hi)
    · intro hxy
      subst y
      funext i
      simp [c, d]
  by_cases hxy : x = y
  · subst y
    have hcard : Fintype.card {i : Fin 10 // i ∉ A} = 5 := by
      rw [Fintype.card_subtype_compl (fun i : Fin 10 => i ∈ A)]
      simpa [hA] using (show Fintype.card (Fin 10) - A.card = 5 by simp [hA])
    have hczero : c = 0 := hc.mpr rfl
    rw [if_pos hczero]
    simp [d, b, graphPhase, hcard]
  · have hc0 : c ≠ 0 := fun hc0 => hxy (hc.mp hc0)
    simp [hc0, hxy]

/-- For an arbitrary index type `ι`, a function `ι → Fin 10` is the same thing as a pair of
functions `ι → ZMod 2` and `ι → ZMod 5`, split pointwise by `bitPart` and `quintPart`. -/
def splitFunctionsEquiv (ι : Type*) :
    (ι → Fin 10) ≃ (ι → ZMod 2) × (ι → ZMod 5) where
  toFun z := (fun i => bitPart (z i), fun i => quintPart (z i))
  invFun z := fun i => localPartsEquiv.symm (z.1 i, z.2 i)
  left_inv z := by
    funext i
    exact localPartsEquiv.symm_apply_apply (z i)
  right_inv z := by
    apply Prod.ext
    · funext i
      exact congrArg Prod.fst (localPartsEquiv.apply_symm_apply (z.1 i, z.2 i))
    · funext i
      exact congrArg Prod.snd (localPartsEquiv.apply_symm_apply (z.1 i, z.2 i))

@[simp] lemma bitPart_localPartsEquiv_symm (u : ZMod 2) (v : ZMod 5) :
    bitPart (localPartsEquiv.symm (u, v)) = u := by
  exact congrArg Prod.fst (localPartsEquiv.apply_symm_apply (u, v))

@[simp] lemma quintPart_localPartsEquiv_symm (u : ZMod 2) (v : ZMod 5) :
    quintPart (localPartsEquiv.symm (u, v)) = v := by
  exact congrArg Prod.snd (localPartsEquiv.apply_symm_apply (u, v))

lemma ameAmplitude_paste_split (A : Finset (Fin 9)) (x : A → Fin 10)
    (u : {i : Fin 9 // i ∉ A} → ZMod 2)
    (v : {i : Fin 9 // i ∉ A} → ZMod 5) :
    ameAmplitude (pasteOn A x
      ((splitFunctionsEquiv {i : Fin 9 // i ∉ A}).symm (u, v))) =
      ((Real.sqrt (2 ^ 11 * 5 ^ 9 : ℝ) : ℂ)⁻¹) *
        ∑ a : Fin 2 → ZMod 2,
          ZMod.stdAddChar
              (binaryPhase a (pasteOn A (fun i => bitPart (x i)) u)) *
            ZMod.stdAddChar
              (quinaryPhase a (pasteOn A (fun i => quintPart (x i)) v)) := by
  unfold ameAmplitude
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  congr 2
  · congr 1
    funext i
    by_cases hi : i ∈ A <;> simp [pasteOn, splitFunctionsEquiv, hi]
  · congr 1
    funext i
    by_cases hi : i ∈ A <;> simp [pasteOn, splitFunctionsEquiv, hi]

lemma ameAmplitude_paste_sum (A : Finset (Fin 9)) (hA : A.card = 4)
    (x y : A → Fin 10) :
    (∑ z : {i : Fin 9 // i ∉ A} → Fin 10,
      ameAmplitude (pasteOn A x z) * star (ameAmplitude (pasteOn A y z))) =
      if x = y then ((10 ^ 4 : ℂ)⁻¹) else 0 := by
  let xb : A → ZMod 2 := fun i => bitPart (x i)
  let yb : A → ZMod 2 := fun i => bitPart (y i)
  let xq : A → ZMod 5 := fun i => quintPart (x i)
  let yq : A → ZMod 5 := fun i => quintPart (y i)
  let C : ℂ := (Real.sqrt (2 ^ 11 * 5 ^ 9 : ℝ) : ℂ)⁻¹
  have hparts : x = y ↔ xb = yb ∧ xq = yq := by
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨hb, hq⟩
      funext i
      apply localPartsEquiv.injective
      rw [localPartsEquiv_apply, localPartsEquiv_apply]
      exact Prod.ext (congrFun hb i) (congrFun hq i)
  rw [← (splitFunctionsEquiv {i : Fin 9 // i ∉ A}).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp_rw [ameAmplitude_paste_split]
  change (∑ u, ∑ v,
    (C * ∑ a, ZMod.stdAddChar (binaryPhase a (pasteOn A xb u)) *
        ZMod.stdAddChar (quinaryPhase a (pasteOn A xq v))) *
      (starRingEnd ℂ) (C * ∑ b,
        ZMod.stdAddChar (binaryPhase b (pasteOn A yb u)) *
        ZMod.stdAddChar (quinaryPhase b (pasteOn A yq v)))) = _
  simp_rw [map_mul, map_sum]
  have hstar (b : Fin 2 → ZMod 2)
      (u : {i : Fin 9 // i ∉ A} → ZMod 2)
      (v : {i : Fin 9 // i ∉ A} → ZMod 5) :
      (starRingEnd ℂ)
          (ZMod.stdAddChar (binaryPhase b (pasteOn A yb u)) *
            ZMod.stdAddChar (quinaryPhase b (pasteOn A yq v))) =
        (starRingEnd ℂ) (ZMod.stdAddChar (binaryPhase b (pasteOn A yb u))) *
          (starRingEnd ℂ) (ZMod.stdAddChar (quinaryPhase b (pasteOn A yq v))) := by
    exact map_mul (starRingEnd ℂ) _ _
  simp_rw [hstar]
  rw [sum_product_separable]
  have hqsum (a b : Fin 2 → ZMod 2) :
      (∑ v : {i : Fin 9 // i ∉ A} → ZMod 5,
        ZMod.stdAddChar (quinaryPhase a (pasteOn A xq v)) *
          (starRingEnd ℂ) (ZMod.stdAddChar (quinaryPhase b (pasteOn A yq v)))) =
        if a = b ∧ xq = yq then (5 ^ 5 : ℂ) else 0 :=
    quinary_phase_physical_sum A hA a b xq yq
  simp_rw [hqsum]
  by_cases hq : xq = yq
  · have hx_iff : x = y ↔ xb = yb := by simpa [hq] using hparts
    simp only [hq, and_true]
    simp_rw [mul_ite]
    simp only [mul_zero, Fintype.sum_ite_eq]
    rw [← Finset.sum_mul]
    have hbsum :
        (∑ a : Fin 2 → ZMod 2,
          ∑ u : {i : Fin 9 // i ∉ A} → ZMod 2,
            ZMod.stdAddChar (binaryPhase a (pasteOn A xb u)) *
              (starRingEnd ℂ) (ZMod.stdAddChar
                (binaryPhase a (pasteOn A yb u)))) =
          if xb = yb then (2 ^ 7 : ℂ) else 0 :=
      q2_phase_paste_sum A hA xb yb
    rw [hbsum]
    by_cases hb : xb = yb
    · rw [if_pos hb, if_pos (hx_iff.mpr hb)]
      dsimp [C]
      norm_num [map_inv₀]
      have hs : Real.sqrt (4000000000 : ℝ) ^ 2 = 4000000000 :=
        Real.sq_sqrt (by norm_num)
      have hnR : Real.sqrt (4000000000 : ℝ) ≠ 0 := by positivity
      have hn : (Real.sqrt (4000000000 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast hnR
      field_simp
      exact_mod_cast hs.symm
    · rw [if_neg hb, if_neg (fun h => hb (hx_iff.mp h))]
      ring
  · have hxy : x ≠ y := fun h => hq (hparts.mp h).2
    simp [hq, hxy]

lemma ameState_norm_sq_sum :
    (∑ w : Config 9 10, ‖ameAmplitude w‖ ^ 2) = 1 := by
  let A : Finset (Fin 9) := Finset.univ.filter (fun i => i.1 < 4)
  have hA : A.card = 4 := by decide
  apply Complex.ofReal_injective
  push_cast
  rw [← (Equiv.piEquivPiSubtypeProd (fun i : Fin 9 => i ∈ A) (fun _ => Fin 10)).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  have hn (z : ℂ) : (↑‖z‖ : ℂ) ^ 2 = z * star z := by
    exact (RCLike.mul_conj z).symm
  simp_rw [hn]
  change (∑ x : A → Fin 10, ∑ z : {i : Fin 9 // i ∉ A} → Fin 10,
    ameAmplitude (pasteOn A x z) * star (ameAmplitude (pasteOn A x z))) = 1
  have hc (x : A → Fin 10) :
      (∑ z : {i : Fin 9 // i ∉ A} → Fin 10,
        ameAmplitude (pasteOn A x z) * star (ameAmplitude (pasteOn A x z))) =
        ((10 ^ 4 : ℂ)⁻¹) := by
    simpa using ameAmplitude_paste_sum A hA x x
  simp_rw [hc]
  simp [Fintype.card_fun, Fintype.card_coe, hA]
  norm_num

lemma ameState_normalized : IsNormalized ameState := by
  rw [IsNormalized, EuclideanSpace.norm_eq]
  change Real.sqrt (∑ w : Config 9 10, ‖ameAmplitude w‖ ^ 2) = 1
  rw [ameState_norm_sq_sum]
  norm_num

/-! ## F. Four-party reductions and the main result -/

/-- The parties `i` with `π i < 4`, that is, the four parties that the permutation `π` moves
into the first four positions. -/
def permFirstSet (π : Equiv.Perm (Fin 9)) : Finset (Fin 9) :=
  Finset.univ.filter (fun i => (π i).1 < 4)

@[simp] lemma permFirstSet_mem (π : Equiv.Perm (Fin 9)) (i : Fin 9) :
    i ∈ permFirstSet π ↔ (π i).1 < 4 := by simp [permFirstSet]

/-- `permFirstSet π` is indexed by `Fin 4` through `π`, by `i ↦ π i`. -/
def permFrontEquiv (π : Equiv.Perm (Fin 9)) : permFirstSet π ≃ Fin 4 where
  toFun i := ⟨(π i.1).1, (permFirstSet_mem π i.1).mp i.2⟩
  invFun k := ⟨π.symm ⟨k.1, by omega⟩, by simp⟩
  left_inv i := by ext; simp
  right_inv k := by ext; simp

/-- The complement of `permFirstSet π` is indexed by `Fin 5` through `π`, by
`i ↦ π i - 4`. -/
def permRestEquiv (π : Equiv.Perm (Fin 9)) :
    {i : Fin 9 // i ∉ permFirstSet π} ≃ Fin 5 where
  toFun i := ⟨(π i.1).1 - 4, by
    have hn : ¬ (π i.1).1 < 4 := by simpa [permFirstSet] using i.2
    have hu : (π i.1).1 < 9 := (π i.1).2
    omega⟩
  invFun k := ⟨π.symm ⟨k.1 + 4, by omega⟩, by
    simp only [permFirstSet_mem, Equiv.apply_symm_apply]
    omega⟩
  left_inv i := by
    apply Subtype.ext
    apply π.injective
    apply Fin.ext
    simp only [Equiv.apply_symm_apply]
    have hn : ¬ (π i.1).1 < 4 := by simpa [permFirstSet] using i.2
    omega
  right_inv k := by
    apply Fin.ext
    simp only [Equiv.apply_symm_apply]
    omega

lemma permFirstSet_card (π : Equiv.Perm (Fin 9)) : (permFirstSet π).card = 4 := by
  rw [← Fintype.card_coe]
  rw [Fintype.card_congr (permFrontEquiv π)]
  simp

lemma permuteConfig_combineFirst_four (π : Equiv.Perm (Fin 9))
    (x : Config 4 10) (z : Config 5 10) :
    permuteConfig π (combineFirst 4 (by omega) x z) =
      pasteOn (permFirstSet π) (fun i => x (permFrontEquiv π i))
        (fun i => z (permRestEquiv π i)) := by
  funext i
  by_cases hi : i ∈ permFirstSet π
  · simp only [permuteConfig, combineFirst, pasteOn, hi, ↓reduceDIte]
    rw [dif_pos ((permFirstSet_mem π i).mp hi)]
    rfl
  · simp only [permuteConfig, combineFirst, pasteOn, hi, ↓reduceDIte]
    have hn : ¬(π i).1 < 4 := by simpa using hi
    rw [dif_neg hn]
    rfl

lemma ameState_reduction_permuted (π : Equiv.Perm (Fin 9)) :
    HasMaximallyMixedFirstReduction (n := 9) (d := 10)
      (9 / 2) (Nat.div_le_self 9 2) (permuteState π ameState) := by
  unfold HasMaximallyMixedFirstReduction
  ext x y
  change (∑ z : Config 5 10,
    ameAmplitude (permuteConfig π (combineFirst 4 (by omega) x z)) *
      star (ameAmplitude (permuteConfig π (combineFirst 4 (by omega) y z)))) = _
  simp_rw [permuteConfig_combineFirst_four]
  let A := permFirstSet π
  let xb : A → Fin 10 := fun i => x (permFrontEquiv π i)
  let yb : A → Fin 10 := fun i => y (permFrontEquiv π i)
  let e : Config 5 10 ≃ ({i : Fin 9 // i ∉ A} → Fin 10) :=
    Equiv.arrowCongr (permRestEquiv π).symm (Equiv.refl (Fin 10))
  change (∑ z : Config 5 10,
    ameAmplitude (pasteOn A xb (e z)) * star (ameAmplitude (pasteOn A yb (e z)))) = _
  calc
    _ = ∑ z : {i : Fin 9 // i ∉ A} → Fin 10,
        ameAmplitude (pasteOn A xb z) * star (ameAmplitude (pasteOn A yb z)) :=
      e.sum_comp (fun z =>
        ameAmplitude (pasteOn A xb z) * star (ameAmplitude (pasteOn A yb z)))
    _ = if xb = yb then ((10 ^ 4 : ℂ)⁻¹) else 0 :=
      ameAmplitude_paste_sum A (permFirstSet_card π) xb yb
    _ = _ := by
      have hxy : xb = yb ↔ x = y := by
        constructor
        · intro h
          funext k
          obtain ⟨i, rfl⟩ := (permFrontEquiv π).surjective k
          exact congrFun h i
        · rintro rfl
          rfl
      simp only [hxy]
      by_cases h : x = y
      · subst y
        simp [maximallyMixed, Fintype.card_fun]
        norm_num
      · simp [maximallyMixed, Fintype.card_fun, h]


/--
**An $\mathrm{AME}(9, 10)$ state exists**, that is, a pure state of nine ten-level systems
whose every four-party reduced density matrix is maximally mixed. This is the case
$(n, d) = (9, 10)$ of Open Quantum Problem 35; `ameState` is the witness.

Statement copied verbatim from `FormalConjectures/OpenQuantumProblems/35.lean`
(`OpenQuantumProblem35.ame_9_10_open`), via the abbreviation `ame_9_10_open_statement`.
-/
lemma ame_9_10_open :
    ame_9_10_open_statement := by
  unfold ame_9_10_open_statement ExistsAME IsAME
  exact ⟨ameState, ameState_normalized, ameState_reduction_permuted⟩


end OpenQuantumProblem35
