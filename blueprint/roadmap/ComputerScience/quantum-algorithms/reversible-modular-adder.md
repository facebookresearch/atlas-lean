# Reversible modular adder

Fix the gate set NOT, CNOT and Toffoli, count gates, and call an ancilla clean if it starts and ends in $0$. Let
$N \ge 1$ and let $n \in \mathbb{N}$ with $2^n \ge N$. There is a circuit over this gate set on two $n$-bit registers and
$O(n)$ clean ancillas, with $O(n)$ gates, that realizes the permutation of the basis states of the two registers mapping
$\lvert a, b \rangle$ to $\lvert a, (a + b) \bmod N \rangle$ whenever $0 \le a, b < N$ and leaving $\lvert a, b \rangle$ unchanged
otherwise. For each fixed $a < N$, $b \mapsto (a + b) \bmod N$ is a bijection of $\{0, \dots, N-1\}$, so this assignment is
a permutation; the arithmetic contract alone, stated only on valid residues, does not determine a reversible circuit,
and being a permutation does not by itself bound the circuit size.

One construction: compute into a fresh ancilla a flag recording $a < N$ and $b < N$, by a comparator circuit. Every
following step is controlled by the flag: compute $s = (a + b) \bmod N$ into a fresh register by reversibly simulating
linear-size Boolean addition, comparison and subtraction circuits; erase $b$ by adding into the $b$ register, bitwise
modulo $2$, the value $(s - a) \bmod N = b$, computed reversibly with scratch space that is then uncomputed; exchange the
two registers. Since $(a, (a + b) \bmod N)$ is again a pair of valid residues, the flag is then erased by recomputing the
same comparison on the final registers. On invalid inputs nothing is changed. Each step uses $O(n)$ gates and clean
ancillas.

## Expansion

This node states a precise result. A good expansion adds a page for each pending prerequisite below.

- Proof prerequisite: linear-size Boolean circuits for $n$-bit addition, subtraction and comparison.
- Proof prerequisite: for each width $w$ and constant $c$ with $0 \le c \le 2^w$, a clean comparator circuit mapping
  $\lvert r \rangle \lvert t \rangle$ to $\lvert r \rangle \lvert t \oplus [r < c] \rangle$ for every $w$-bit $r$, using clean ancillas; for
  $c = 0$ it acts as the identity and for $c = 2^w$ as an unconditional $X$ on the target.

## Proof depends on

- [Reversible simulation of classical circuits](../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/reversible-simulation-of-classical-circuits.md)

## Sources

- P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum
  computer*, SIAM Journal on Computing 26 (1997); arXiv:quant-ph/9508027v2, Section 3.
  <https://arxiv.org/abs/quant-ph/9508027>
