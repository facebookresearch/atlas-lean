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

/-- **Initial state of a QMA verifier.** For a bitstring $x = (x_0, \dots, x_{n-1})$, with true
read as $1$ and false as $0$, numbers $m$ and $a$, and a vector $\psi \in \mathbb{C}^{2^m}$ (the
witness on $m$ qubits), the initial state is the tensor product of the computational basis state
of $x$, the vector $\psi$ and the all-zero state on $a$ ancilla qubits, in this order. It is the
vector on $\{0, \dots, 2^{n+m+a} - 1\}$ whose value at $s$ is $\psi(\lfloor s / 2^n \rfloor)$ if
$s < 2^{n+m}$ and $s \bmod 2^n = \sum_{k < n} x_k 2^k$, and $0$ otherwise. So $x$ occupies the
$n$ low-order bits of the index, the witness the next $m$ bits and the ancillas the $a$
high-order bits. -/
def initState (x : List Bool) (m a : ℕ) (ψ : Fin (2 ^ m) → ℂ) :
    Fin (2 ^ (x.length + m + a)) → ℂ :=
  tensorProd (tensorProd (basisState x) ψ) (zeroState a)

/-- **QMA for promise problems.** A pair $(\Pi_{\mathrm{yes}}, \Pi_{\mathrm{no}})$ of sets of
bitstrings is in QMA when there are polynomials $m$, $a$ and $s$ with natural-number coefficients
and a polynomial-time computable map sending each bitstring $x$ to a list of encoded 2-local
quantum gates such that, for every bitstring $x$, writing $N = |x| + m(|x|) + a(|x|)$: the list
has at most $s(|x|)$ gates, each well-formed on $N$ qubits; if $x \in \Pi_{\mathrm{yes}}$, some
state $\psi$ on $m(|x|)$ qubits with squared norm $1$ makes the acceptance probability of the
circuit, applied to the tensor product of the basis state of $x$, $\psi$ and the all-zero state
on $a(|x|)$ qubits, at least $2/3$; and if $x \in \Pi_{\mathrm{no}}$, every state $\psi$ on
$m(|x|)$ qubits with squared norm $1$ makes this acceptance probability at most $1/3$.

No condition is imposed on bitstrings outside $\Pi_{\mathrm{yes}} \cup \Pi_{\mathrm{no}}$. -/
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

/-- **Polynomial-time reduction between promise problems.** A promise problem $(Y_1, N_1)$,
given by sets $Y_1$ and $N_1$ of bitstrings, reduces to another such promise problem $(Y_2, N_2)$
when there is a polynomial-time computable map $f$ from bitstrings to bitstrings with
$f(x) \in Y_2$ for every $x \in Y_1$ and $f(x) \in N_2$ for every $x \in N_1$. -/
def PromiseReduces (Yes₁ No₁ Yes₂ No₂ : Set (List Bool)) : Prop :=
  ∃ f : List Bool → List Bool, IsPolyTime f ∧
    (∀ x ∈ Yes₁, f x ∈ Yes₂) ∧ (∀ x ∈ No₁, f x ∈ No₂)

/-- **Encoded 2-local Hamiltonian term.** A 2-local Hamiltonian term is encoded as a triple
$(i, j, e)$ of natural numbers $i$ and $j$, the qubits it acts on, and a list $e$ of pairs of
encoded rational numbers, the real and imaginary parts of the entries of its $4 \times 4$ matrix
in row-major order.

The encoding itself does not require $e$ to have $16$ entries or the matrix to be Hermitian; the
qubit bounds, the number of entries and positive semidefiniteness (hence Hermiticity) are part of
the validity of a term. -/
abbrev LocalTerm := ℕ × ℕ × List (RatEnc × RatEnc)

open Classical in
/-- **Embedding of a 2-local term into $n$ qubits.** Let a 2-local term act on qubits $i$ and $j$,
and let $M$ be the $4 \times 4$ complex matrix encoded by its list of entries, with rows and
columns indexed by pairs of bits. Its embedding into $n$ qubits is the $2^n \times 2^n$ complex
matrix whose entry at basis indices $s, t \in \{0, \dots, 2^n - 1\}$ is
$M_{(s_i, s_j), (t_i, t_j)}$ if $s_k = t_k$ for every $k \ne i, j$, and $0$ otherwise, where
$s_k = \lfloor s / 2^k \rfloor \bmod 2$ is bit $k$ of $s$.

When $i \ne j$ and $i, j < n$, this is $M$ acting on qubits $i$ and $j$, tensored with the
identity on the other qubits. -/
noncomputable def embedTerm (n : ℕ) (term : LocalTerm) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun s t =>
    if (∀ k, k ≠ term.1 → k ≠ term.2.1 → qBit k s.val = qBit k t.val) then
      (matrixOfEntries term.2.2) (qBit term.1 s.val, qBit term.2.1 s.val)
        (qBit term.1 t.val, qBit term.2.1 t.val)
    else 0

/-- **Hamiltonian of a list of 2-local terms.** For a number $n$ of qubits and a list
$h_1, \dots, h_m$ of 2-local terms, the Hamiltonian is the $2^n \times 2^n$ complex matrix
$\tilde h_1 + \dots + \tilde h_m$, where $\tilde h_l$ is the embedding of $h_l$ into $n$ qubits;
for the empty list it is the zero matrix. -/
noncomputable def hamiltonian (n : ℕ) (terms : List LocalTerm) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (terms.map (embedTerm n)).foldl (· + ·) 0

open Classical in
/-- **Ground energy of a Hermitian matrix.** For a natural number $n$, the ground energy of a
Hermitian $2^n \times 2^n$ complex matrix $H$ is the smallest eigenvalue of $H$. -/
noncomputable def groundEnergy {n : ℕ} (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hH : H.IsHermitian) : ℝ :=
  Finset.min' (Finset.univ.image hH.eigenvalues)
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- **Valid 2-local Hamiltonian term.** A 2-local term acting on qubits $i$ and $j$ with entry
list $e$ is valid on $n$ qubits when $i < j < n$, the list $e$ has exactly $16$ entries, each
entry has nonzero denominators in the encodings of both its real and its imaginary part, the
$4 \times 4$ complex matrix $M$ encoded by $e$ is positive semidefinite, and
$\sum_{p, q} |M_{pq}|^2 \le 1$, that is, $M$ has Frobenius norm at most $1$.

In particular $M$ is Hermitian and has operator norm at most $1$. -/
def localTermValid (n : ℕ) (term : LocalTerm) : Prop :=
  term.1 < term.2.1 ∧ term.2.1 < n ∧ term.2.2.length = 16 ∧
  (∀ e ∈ term.2.2, e.1.2.2 ≠ 0 ∧ e.2.2.2 ≠ 0) ∧
  (matrixOfEntries term.2.2).PosSemidef ∧
  (Finset.univ.sum (fun p : Fin 2 × Fin 2 => Finset.univ.sum
    (fun q : Fin 2 × Fin 2 => ((matrixOfEntries term.2.2) p q).re ^ 2 +
      ((matrixOfEntries term.2.2) p q).im ^ 2))) ≤ (1 : ℝ)

open Classical in
/-- **Yes-instances of the 2-local Hamiltonian problem.** A bitstring $x$ is a yes-instance when
decoding it under the canonical bitstring encoding gives a tuple $(n, (h_1, \dots, h_m), a, b)$ of
a natural number $n$, a list of 2-local terms $h_1, \dots, h_m$ and two encoded rational numbers,
whose values we also write $a$ and $b$, such that every $h_l$ is valid on $n$ qubits,
$b - a \ge 1/(m + 1)$, and the Hamiltonian $H$ of $h_1, \dots, h_m$ on $n$ qubits is Hermitian
and has ground energy at most $a$. -/
def LocalHamYes : Set (List Bool) :=
  {x | ∃ (n : ℕ) (terms : List LocalTerm) (a b : RatEnc),
    MetaMathlibExt.BitstringEncoding.bitDecode x = some (n, terms, a, b) ∧
    (∀ term ∈ terms, localTermValid n term) ∧
    (1 : ℚ) / ((terms.length : ℚ) + 1) ≤ (toRat b : ℚ) - (toRat a : ℚ) ∧
    ∃ hH : (hamiltonian n terms).IsHermitian,
      groundEnergy (hamiltonian n terms) hH ≤ ((toRat a : ℚ) : ℝ)}

/-- **No-instances of the 2-local Hamiltonian problem.** A bitstring $x$ is a no-instance when
decoding it under the canonical bitstring encoding gives a tuple $(n, (h_1, \dots, h_m), a, b)$ of
a natural number $n$, a list of 2-local terms $h_1, \dots, h_m$ and two encoded rational numbers,
whose values we also write $a$ and $b$, such that every $h_l$ is valid on $n$ qubits,
$b - a \ge 1/(m + 1)$, and the Hamiltonian $H$ of $h_1, \dots, h_m$ on $n$ qubits is Hermitian
and has ground energy at least $b$. -/
def LocalHamNo : Set (List Bool) :=
  {x | ∃ (n : ℕ) (terms : List LocalTerm) (a b : RatEnc),
    MetaMathlibExt.BitstringEncoding.bitDecode x = some (n, terms, a, b) ∧
    (∀ term ∈ terms, localTermValid n term) ∧
    (1 : ℚ) / ((terms.length : ℚ) + 1) ≤ (toRat b : ℚ) - (toRat a : ℚ) ∧
    ∃ hH : (hamiltonian n terms).IsHermitian,
      ((toRat b : ℚ) : ℝ) ≤ groundEnergy (hamiltonian n terms) hH}

/-- **The 2-local Hamiltonian problem is QMA-complete.** The 2-local Hamiltonian promise
problem, given by its yes-instances and no-instances, is in QMA, and every promise problem in QMA
whose sets of yes-instances and no-instances are disjoint sets of bitstrings has a polynomial-time
reduction to it.

Here an instance encodes a number $n$ of qubits, a list of $m$ valid 2-local terms on $n$ qubits
and encoded rationals $a$ and $b$ with $b - a \ge 1/(m + 1)$; it is a yes-instance when the
Hamiltonian of the terms on $n$ qubits is Hermitian with ground energy at most $a$, and a
no-instance when it is Hermitian with ground energy at least $b$.

Source: A. Y. Kitaev, "Quantum
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
