# Shor per-outcome probability bound (asymptotic source form)

Let $N \ge 2$, $x$ a unit modulo $N$ of order $r$, and $q = 2^L$ with $N^2 \le q < 2N^2$. In Shor's period-finding state after the
Fourier transform, consider an outcome $(c, x^k \bmod N)$ with $0 \le c < q$ and $0 \le k < r$ such that some integer $d$
satisfies $-r/2 \le rc - dq \le r/2$. Shor's estimate shows that its probability is asymptotically bounded below by
$4/(\pi^2 r^2)$ and therefore at least $1/(3r^2)$ for $N$ sufficiently large. This is an asymptotic statement: the source gives no explicit threshold on $N$; a version with a stated constant and
threshold is a separate page.

## Depends on

- [Quantum Fourier transform matrix](../../QuantumInformation/quantum-operations/quantum-fourier-transform/qft-matrix.md)

## Sources

- Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer (arXiv:quant-ph/9508027v2) — P. W. Shor (SIAM J. Comput. 26 (1997)). <https://arxiv.org/pdf/quant-ph/9508027> Section 5, equations (5.11)–(5.13) and the bound $1/(3r^2)$ per state.
