/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Local Hamiltonian problem is QMA-complete

Source:
A. Y. Kitaev, "Quantum NP", talk at AQIP 1999; A. Y. Kitaev, A. H. Shen, and M. N.
Vyalyi, Classical and Quantum Computation, American Mathematical Society, 2002, Section
14.4; J. Kempe, A. Y. Kitaev, and O. Regev, "The complexity of the local Hamiltonian
problem", SIAM Journal on Computing 35 (2006), 1070-1097 (the 2-local reduction,
reducing Kitaev's 5-local result to 3-local and then to 2-local); A. D. Bookatz,
"QMA-complete problems", arXiv:1212.6312 (2012), Section 2 (survey of the
QMA-completeness of the local Hamiltonian problem); S. Arora and B. Barak, Computational
Complexity: A Modern Approach, 2009, Chapter 10, for the QMA-completeness of 2-local
Hamiltonian.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.LocalHamiltonianQMA

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory
open scoped ComplexOrder

/-!
# The Local Hamiltonian problem is QMA-complete

`QMA` is the quantum analogue of `NP`, stated here as a class of *promise problems*:
there is a uniform family of polynomial-size quantum verifier circuits (2-local unitary
gates with rational entries, generated in polynomial time) such that, on a yes-instance,
some poly-size quantum witness state makes the verifier accept with probability `≥ 2/3`,
while on a no-instance every witness makes it accept with probability `≤ 1/3`. States are
vectors `Fin (2 ^ N) → ℂ` indexed by computational basis states; bit `k` of index `i`
is `(i / 2 ^ k) % 2`; a gate applies its `4 × 4` unitary to the two addressed qubits.

The quantum-circuit API (`RatEnc`, `toRat`, `toComplex`, `qBit`, `qIdx2`,
`matrixOfEntries`, `setBits`, `QGate`, `QGateWellFormed`, `applyGate`,
`applyCircuit`, `qNumOf`, `basisState`, `tensorProd`, `zeroState`, `sqNorm`,
`acceptProb`) is the canonical one in `CSLibExt/Computability/Complexity/Classes.lean`,
shared with `BQP`; this file keeps only its source-specific definitions
(`initState`, `QMAPromise`, `PromiseReduces`, `LocalTerm`,
`embedTerm`, `hamiltonian`, `groundEnergy`, `localTermValid`, `LocalHamYes`,
`LocalHamNo`).

The Local Hamiltonian problem: given `n` qubits, a list of 2-local terms (Hermitian
`4 × 4` matrices with rational entries, acting on pairs of qubits) and thresholds `a < b`,
is the ground energy of the sum at most `a`? It is `QMA`-complete as a promise problem:
the promise is that the ground energy is `≤ a` or `≥ b` with `b - a` inverse-polynomial
in the number of terms (both thresholds carried in the encoding); it is in `QMA` (the
verifier checks a witness's energy), and every `QMA` promise problem reduces to it
(Kitaev's circuit-to-Hamiltonian construction). An exact threshold comparison with the
second threshold discarded would not be the QMA promise problem, so the promise gap is
part of the yes/no instance sets. Instance validation is more than Hermiticity: every
term must have exactly 16 entries with nonzero denominators, be positive semidefinite
(so `0 ≤ H_i`, with Hermiticity implied), and have Frobenius norm at most `1` (hence
operator norm at most `1`); without a norm bound, exponentially large coefficients would
make the absolute inverse-polynomial gap exponentially small after normalization, and
the usual QMA verifier would not establish the promise pair.
-/

/-- The initial state of the verifier: input `x`, witness `ψ` on `m` qubits, `a`
ancilla qubits in state `0`. -/
def initState (x : List Bool) (m a : ℕ) (ψ : Fin (2 ^ m) → ℂ) :
    Fin (2 ^ (x.length + m + a)) → ℂ :=
  tensorProd (tensorProd (basisState x) ψ) (zeroState a)

/-- `QMA` for promise problems: a promise problem `(Yes, No)` (disjoint sets of
instances) is in `QMA` if there is a uniform family of polynomial-size quantum verifier
circuits (2-local unitary gates with rational entries, generated in polynomial time)
such that, on a yes-instance, some poly-size quantum witness state makes the verifier
accept with probability `≥ 2/3`, while on a no-instance every witness makes it accept
with probability `≤ 1/3`. No condition is imposed outside the promise. -/
def QMAPromise (Yes No : Set (List Bool)) : Prop :=
  ∃ (m a s : Polynomial ℕ) (gates : List Bool → List QGate),
    IsPolyTime gates ∧
    (∀ x, (gates x).length ≤ s.eval x.length) ∧
    (∀ x, ∀ g ∈ gates x,
      QGateWellFormed (x.length + m.eval x.length + a.eval x.length) g) ∧
    (∀ x ∈ Yes,
      ∃ ψ : Fin (2 ^ (m.eval x.length)) → ℂ, sqNorm ψ = 1 ∧
        2 / 3 ≤ acceptProb
          (applyCircuit (x.length + m.eval x.length + a.eval x.length)
            (gates x) (initState x (m.eval x.length) (a.eval x.length) ψ))) ∧
    (∀ x ∈ No,
      ∀ ψ : Fin (2 ^ (m.eval x.length)) → ℂ, sqNorm ψ = 1 →
        acceptProb
          (applyCircuit (x.length + m.eval x.length + a.eval x.length)
            (gates x) (initState x (m.eval x.length) (a.eval x.length) ψ)) ≤ 1 / 3)

/-- A polynomial-time reduction between promise problems: a poly-time map sending
yes-instances to yes-instances and no-instances to no-instances. -/
def PromiseReduces (Yes₁ No₁ Yes₂ No₂ : Set (List Bool)) : Prop :=
  ∃ f : List Bool → List Bool, IsPolyTime f ∧
    (∀ x ∈ Yes₁, f x ∈ Yes₂) ∧ (∀ x ∈ No₁, f x ∈ No₂)

/-- A 2-local Hamiltonian term: the two qubits it acts on, and its `4 × 4` Hermitian
matrix (as a list of 16 rational pairs). -/
abbrev LocalTerm := ℕ × ℕ × List (RatEnc × RatEnc)

open Classical in
/-- A 2-local term embedded into the full `n`-qubit Hilbert space. -/
noncomputable def embedTerm (n : ℕ) (term : LocalTerm) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun s t =>
    if (∀ k, k ≠ term.1 → k ≠ term.2.1 → qBit k s.val = qBit k t.val) then
      (matrixOfEntries term.2.2) (qBit term.1 s.val, qBit term.2.1 s.val)
        (qBit term.1 t.val, qBit term.2.1 t.val)
    else 0

/-- The Hamiltonian of a list of 2-local terms: their sum. -/
noncomputable def hamiltonian (n : ℕ) (terms : List LocalTerm) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (terms.map (embedTerm n)).foldl (· + ·) 0

open Classical in
/-- The ground energy of a Hermitian matrix: its smallest eigenvalue. -/
noncomputable def groundEnergy {n : ℕ} (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hH : H.IsHermitian) : ℝ :=
  Finset.min' (Finset.univ.image hH.eigenvalues)
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- A 2-local term is valid: it addresses two distinct qubits below `n`, has exactly
16 entries with nonzero denominators, is positive semidefinite, and has Frobenius
norm at most `1` (so operator norm at most `1`). -/
def localTermValid (n : ℕ) (term : LocalTerm) : Prop :=
  term.1 < term.2.1 ∧ term.2.1 < n ∧ term.2.2.length = 16 ∧
  (∀ e ∈ term.2.2, e.1.2.2 ≠ 0 ∧ e.2.2.2 ≠ 0) ∧
  (matrixOfEntries term.2.2).PosSemidef ∧
  (Finset.univ.sum (fun p : Fin 2 × Fin 2 => Finset.univ.sum
    (fun q : Fin 2 × Fin 2 => ((matrixOfEntries term.2.2) p q).re ^ 2 +
      ((matrixOfEntries term.2.2) p q).im ^ 2))) ≤ (1 : ℝ)

open Classical in
/-- The yes-instances of the Local Hamiltonian promise problem: instances decoding
to `(n, terms, a, b)` with valid 2-local terms (see `localTermValid`) and an
inverse-polynomial promise gap `b - a ≥ 1 / (number of terms + 1)`, whose ground
energy is at most `a`. -/
def LocalHamYes : Set (List Bool) :=
  {x | ∃ (n : ℕ) (terms : List LocalTerm) (a b : RatEnc),
    MetaMathlibExt.BitstringEncoding.bitDecode x = some (n, terms, a, b) ∧
    (∀ term ∈ terms, localTermValid n term) ∧
    (1 : ℚ) / ((terms.length : ℚ) + 1) ≤ (toRat b : ℚ) - (toRat a : ℚ) ∧
    ∃ hH : (hamiltonian n terms).IsHermitian,
      groundEnergy (hamiltonian n terms) hH ≤ ((toRat a : ℚ) : ℝ)}

/-- The no-instances of the Local Hamiltonian promise problem: as in `LocalHamYes`,
but with ground energy at least `b`. -/
def LocalHamNo : Set (List Bool) :=
  {x | ∃ (n : ℕ) (terms : List LocalTerm) (a b : RatEnc),
    MetaMathlibExt.BitstringEncoding.bitDecode x = some (n, terms, a, b) ∧
    (∀ term ∈ terms, localTermValid n term) ∧
    (1 : ℚ) / ((terms.length : ℚ) + 1) ≤ (toRat b : ℚ) - (toRat a : ℚ) ∧
    ∃ hH : (hamiltonian n terms).IsHermitian,
      ((toRat b : ℚ) : ℝ) ≤ groundEnergy (hamiltonian n terms) hH}

/-- **The Local Hamiltonian problem is QMA-complete.** Source: A. Y. Kitaev, "Quantum
NP", talk at AQIP 1999; A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4; J. Kempe, A. Y. Kitaev,
and O. Regev, "The complexity of the local Hamiltonian problem", SIAM Journal on
Computing 35 (2006), 1070-1097 (the 2-local reduction); A. D. Bookatz,
"QMA-complete problems", arXiv:1212.6312 (2012), Section 2 (survey of the
QMA-completeness of the local Hamiltonian problem); S. Arora and B. Barak, Computational
Complexity: A Modern Approach, 2009, Chapter 10, for the QMA-completeness of 2-local
Hamiltonian. -/
public theorem_wanted local_hamiltonian_qma_complete :
    QMAPromise LocalHamYes LocalHamNo ∧
    ∀ Yes No : Set (List Bool), Disjoint Yes No → QMAPromise Yes No →
      PromiseReduces Yes No LocalHamYes LocalHamNo

end MetaMathlibExt.Complexity.KeyTheorems.LocalHamiltonianQMA
