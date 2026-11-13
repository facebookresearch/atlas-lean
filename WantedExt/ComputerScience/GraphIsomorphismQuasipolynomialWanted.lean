/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
ALG-016: Babai's theorem on graph isomorphism (resolved). Graph isomorphism
is decidable in quasi-polynomial time for all graphs.

A finite simple graph is presented as a vertex count `n` plus a symmetric,
loop-free adjacency matrix on `Fin n` (`GraphCode`). A decision input is a
pair of such codes, serialized by a transparent prefix-free bit scheme
(`encodePair`: unary lengths, binary magnitudes, row-major adjacency bits).
`Isomorphic G H` holds when the vertex counts agree and some vertex
permutation carries one adjacency matrix to the other. The proposition asks
for one fixed deterministic machine (Mathlib's bundled
`Turing.TM2ComputableInTime`) deciding isomorphism on all pairs, whose time
function is pointwise bounded by the quasipolynomial `qpTime c` for some
fixed exponent `c`, measured in encoded input length.

Representation notes: the quasipolynomial bound `2 ^ ((log2(len+2)+2)^c)`
is stated in the encoded bit length `len`, which is polynomially related
to the vertex count, so this matches the standard `exp((log n)^O(1))`
formulation. Babai's quasipolynomial algorithm itself is NOT formalized
here; this file states only the existence claim, which Babai proved
(STOC 2016; see the registry entry).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.Encoding
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Nat.Log
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

namespace MathlibExt.ComputerScience.GraphIsomorphismQuasipolynomialWanted

/-! Source record `ALG-016`. -/

/-- **Graph codes.** A graph code consists of a vertex count $n \in \mathbb{N}$, with vertices
$0, \dots, n-1$, and a Boolean adjacency matrix $A$ on these vertices that is symmetric
($A_{ij} = A_{ji}$ for all $i, j$) and loop-free ($A_{ii}$ is false for every $i$). -/
structure GraphCode where
  n : ℕ
  adj : Fin n → Fin n → Bool
  symm : ∀ i j, adj i j = adj j i
  irrefl : ∀ i, adj i i = false

/-- **Binary digits of a natural number.** The binary digits of $n \in \mathbb{N}$, most
significant first, as a list of bits with the digit $1$ read as true and $0$ as false; for
$n = 0$ this is the single digit $0$. -/
def natBits (n : ℕ) : List Bool :=
  (Nat.toDigits 2 n).map (fun d => decide (d = '1'))

/-- **Prefix-free encoding of a natural number.** The prefix-free encoding of $n \in \mathbb{N}$
consists of $k$ true bits, where $k$ is the number of binary digits of $n$, then one false bit,
then the binary digits of $n$, most significant first. -/
def natToBits (n : ℕ) : List Bool :=
  List.replicate (natBits n).length true ++ [false] ++ natBits n

/-- **Bit encoding of a graph code.** The bit encoding of a graph code with $n$ vertices and
adjacency matrix $A$ is the prefix-free encoding of $n$ followed by the $n^2$ entries of $A$, as
bits, in row-major order: $A_{0,0}, A_{0,1}, \dots, A_{0,n-1}, A_{1,0}, \dots, A_{n-1,n-1}$. -/
def encode (G : GraphCode) : List Bool :=
  natToBits G.n ++
    ((List.finRange G.n).map fun i =>
      (List.finRange G.n).map fun j => G.adj i j).flatten

/-- **Bit encoding of a pair of graph codes.** The bit encoding of a pair $(G, H)$ of graph codes
is the bit encoding of $G$ followed by the bit encoding of $H$. -/
def encodePair (p : GraphCode × GraphCode) : List Bool :=
  encode p.1 ++ encode p.2

/-- **Isomorphism of graph codes.** Graph codes $G$ and $H$ with adjacency matrices $A$ and $B$
are isomorphic when they have the same vertex count $n$ and there is a permutation $\sigma$ of
the vertices $\{0, \dots, n-1\}$ such that $A_{ij} = B_{\sigma(i)\sigma(j)}$ for all $i, j$. -/
def Isomorphic (G H : GraphCode) : Prop :=
  ∃ h : G.n = H.n, ∃ σ : Equiv.Perm (Fin H.n), ∀ i j : Fin G.n,
    G.adj i j = H.adj (σ (Fin.cast h i)) (σ (Fin.cast h j))

/-- **Quasipolynomial time bound.** For an exponent $c \in \mathbb{N}$ and an input length
$n \in \mathbb{N}$, the quasipolynomial time bound is
$q_c(n) = 2^{(\lfloor \log_2(n+2) \rfloor + 2)^c}$. -/
def qpTime (c n : ℕ) : ℕ :=
  2 ^ ((Nat.log 2 (n + 2) + 2) ^ c)

/-- **The quasipolynomial graph isomorphism statement.** The proposition that graph isomorphism
is decidable in quasipolynomial time: there are a function $D$ from pairs of graph codes to
Booleans, an exponent $c \in \mathbb{N}$, and a deterministic multi-stack Turing machine with a
time function $t : \mathbb{N} \to \mathbb{N}$ that, on the bit encoding of every pair $(G, H)$,
outputs the single bit $D(G, H)$ within $t(\ell)$ steps, where $\ell$ is the length of the
encoding, such that $t(n) \le q_c(n)$ for every $n \in \mathbb{N}$, where $q_c$ is the
quasipolynomial time bound with exponent $c$, and $D(G, H)$ is true if and only if $G$ and $H$
are isomorphic.

Source: ALG-016. -/
def conjecture : Prop :=
  ∃ decideGI : GraphCode × GraphCode → Bool, ∃ c : ℕ,
    ∃ h : Turing.TM2ComputableInTime encodePair Computability.encodeBool decideGI,
      (∀ n : ℕ, h.time n ≤ qpTime c n) ∧
      ∀ G H : GraphCode, decideGI (G, H) = true ↔ Isomorphic G H

/--
**Babai's theorem: graph isomorphism in quasipolynomial time.** The quasipolynomial graph
isomorphism statement holds: there are a function $D$ from pairs of graph codes to Booleans, an
exponent $c \in \mathbb{N}$, and a deterministic multi-stack Turing machine with a time function
$t : \mathbb{N} \to \mathbb{N}$ that, on the bit encoding of every pair $(G, H)$, outputs the
single bit $D(G, H)$ within $t(\ell)$ steps, where $\ell$ is the length of the encoding, such that
$t(n) \le 2^{(\lfloor \log_2(n+2) \rfloor + 2)^c}$ for every $n \in \mathbb{N}$, and $D(G, H)$ is
true if and only if $G$ and $H$ are isomorphic.

Babai (STOC 2016) gave a deterministic quasipolynomial-time graph-isomorphism algorithm; the
corrected proof retains that complexity.

Source: Babai, L., Graph isomorphism in
quasipolynomial time, Proc. 48th ACM Symp. Theory Comput. (STOC 2016), 684-697;
arXiv:1512.03547, https://arxiv.org/abs/1512.03547. Moved from
`OpenConjectures/ComputerScience/GraphIsomorphismQuasipolynomial`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.ComputerScience.GraphIsomorphismQuasipolynomialWanted
