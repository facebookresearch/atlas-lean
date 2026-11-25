# Reversible modular multiplication by a constant unit

Fix the gate set NOT, CNOT and Toffoli, count gates, and call an ancilla clean if it starts and ends in $0$. Let
$N \ge 2$, let $n \in \mathbb{N}$ with $2^n \ge N$, and let $c$ be a unit modulo $N$. There is a circuit over this gate set on an
$n$-bit register and $O(n)$ clean ancillas, with $O(n^2)$ gates, that maps $\lvert y \rangle$ to $\lvert cy \bmod N \rangle$ for
$0 \le y < N$ and leaves $\lvert y \rangle$ unchanged for $N \le y < 2^n$. Every step below, including the exchange of registers
and the uncomputation, is controlled by a flag recording $y < N$, computed and erased by a reversible comparator. Under that
flag the circuit computes $cy \bmod N$ into a fresh register by $n$ controlled reversible modular additions of
$c\,2^i \bmod N$, exchanges the registers, and erases the original contents by subtracting $c^{-1}$ times the new contents
modulo $N$ with the same construction.

The restriction to valid residues and the identity extension are needed: for $N = 3$ and $c = 1$ on two bits, the formula
$y \mapsto cy \bmod N$ applied to every basis state sends both $0$ and $3$ to $0$.

## Proof depends on

- [Reversible modular adder](reversible-modular-adder.md)

## Sources

- P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum
  computer*, SIAM Journal on Computing 26 (1997); arXiv:quant-ph/9508027v2, Section 3.
  <https://arxiv.org/abs/quant-ph/9508027>
