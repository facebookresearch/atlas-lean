# Smoothed Boolean CSPs are refutable at the random-CSP trade-off

For a predicate $P$ whose satisfying assignments support no $t$-wise uniform distribution, the degree-$2\ell$ sum-of-squares relaxation strongly refutes smoothed CSP($P$) instances in time $n^{O(\ell)}$ once there are about $\ell(n/\ell)^{t/2}$ polylogarithmic-factor constraints, matching the trade-off known for fully random instances.

**Theorem (smoothed Boolean CSP refutation).** Let $P:\{\pm1\}^k\to\{0,1\}$ be a $k$-ary predicate such that no $t$-wise uniform distribution is supported on $P^{-1}(1)$, and let $\ell$ be an integer with $2(k-1)\le\ell\le n$. There is an algorithm that takes an instance $\Theta$ of CSP($P$) and outputs $\mathrm{algval}(\Theta)\in[0,1]$ in time $n^{O(\ell)}$ such that:

1. $\mathrm{val}(\Theta)\le\mathrm{algval}(\Theta)\le1$ for every $\Theta$.
2. Suppose $\Theta$ is a $\vec{p}$-smoothing $\psi_s$ of an arbitrary instance $\psi=(\mathcal{H},\Xi)$ with $n$ variables and $m$ constraints, for smoothing parameters $p_{C,i}\in[0,1]$, and suppose $m\ge 2m_0/q(\vec{p})$, where

$$
m_0=\frac{2^{O(k)}(\log_2 n)^{4t+1}}{\epsilon^5}\cdot\ell\left(\frac{n}{\ell}\right)^{t/2},
\qquad
q(\vec{p})=\frac{1}{m}\sum_{C\in\mathcal{H}}\prod_{i\in C}p_{C,i}.
$$

Then with probability at least $1-1/\mathrm{poly}(n)$ over the smoothing,

$$
\mathrm{algval}(\Theta)\le 1-\frac{q(\vec{p})}{2}\,(\delta_t-\epsilon)+2^{-n},
$$

where $\delta_t\ge2^{-\tilde{O}(k^t)}$ depends only on $P$. In the semirandom case (all $p_{C,i}=1$), $\mathrm{algval}(\Theta)\le1-\delta_t+\epsilon+2^{-n}$ with probability $1-1/\mathrm{poly}(n)$.

Moreover, $\mathrm{algval}$ is (to within $2^{-n}$) the value of the canonical degree-$2\ell$ sum-of-squares relaxation of the CSP over the hypercube. The bound is non-trivial when $\epsilon<\delta_t$.

The key ingredient is a certificate for semirandom sparse polynomials. Let $k\in\mathbb{N}$ and $2(k-1)\le\ell(n)\le n$, and let

$$
\phi(x)=\frac{1}{m}\sum_{C\in\mathcal{H}}b_C\prod_{i\le k}x_{C_i}
$$

be a homogeneous multilinear degree-$k$ polynomial given by a $k$-uniform multi-hypergraph $\mathcal{H}$ with $m$ hyperedges and coefficients $b_C$. There is an absolute constant $\Gamma>0$ such that if

$$
n^{\log_2 n}\ge m\ge\Gamma^k\left(\frac{n}{\ell}\right)^{k/2}\ell\cdot\frac{(\log_2 n)^{4k+1}}{\epsilon^5}
$$

and the $b_C$ are independent mean-zero random variables supported in $[-1,1]$, then with probability $1-1/\mathrm{poly}(n)$ every pseudo-expectation $\tilde{\mathbb{E}}$ of degree at least $2\ell$ over $\{\pm1\}^n$ satisfies $\tilde{\mathbb{E}}[\phi]\le\epsilon$; the corresponding $n^{O(\ell)}$-time algorithm outputs a value in $[\max_x\phi(x),\,\epsilon+2^{-n}]$. For semirandom $k$-XOR ($b_C$ uniform signs) this is an $\epsilon$-tight refutation.

Taking $\ell=O(1)$ gives polynomial-time strong refutation of smoothed instances with $\tilde{O}(n^{t/2})$ constraints; for $k$-SAT ($t=k$) and $\ell=n^{\delta}$ it gives $2^{\tilde{O}(n^{\delta})}$-time strong refutation with $\tilde{O}(n^{(1-\delta)k/2+\delta})$ constraints.

## Expansion

Completeness holds because the expectation over a distribution on optimal assignments is a pseudo-expectation. For soundness, let $\mathcal{G}$ be the clauses all of whose $k$ literals are rerandomized; a Chernoff bound gives $|\mathcal{G}|\ge q(\vec{p})m/2\ge m_0$ with high probability. By LP duality (Allen, O'Donnell and Witmer), $P(z)\le1-\delta_t+Q(z)$ on $\{\pm1\}^k$ for a degree-$t$ polynomial $Q$ with no constant term and $\sum_T|\hat{Q}(T)|\le2^{2k}$; since these are inequalities between polynomials in $k$ variables, degree-$2k$ sum-of-squares proves them. This bounds $\tilde{\mathbb{E}}$ of the good part by $1-\delta_t$ plus a combination of the semirandom polynomials $\phi_T(x)=\frac{1}{|\mathcal{G}|}\sum_{C\in\mathcal{G}}b_{C|_T}x_{C|_T}$ with independent $\pm1$ coefficients, each of which the polynomial certificate bounds by $\epsilon/2^{2k}$.

The polynomial certificate itself comes from a level-$\ell$ Kikuchi matrix of the instance, whose quadratic form on tensored assignments encodes $\phi$. A regularity decomposition splits an arbitrary hypergraph into regular bipartite pieces of lower arity plus few error hyperedges; on a regular piece, rows of large butterfly degree are pruned (they are few and contribute little to the $\infty\to1$ norm), the remaining rows are bucketed by degree, and matrix Bernstein bounds the spectral norm of each bucket. Because every step is a spectral bound, it is captured by degree-$2\ell$ sum-of-squares. For fully random CSPs the same trade-off (up to polylogarithmic factors) was shown by Raghavendra, Rao and Schramm, and the Kothari-Mori-O'Donnell-Witmer sum-of-squares lower bound shows it is essentially tight for such algorithms. The same Kikuchi analysis proves Feige's conjecture on even covers of hypergraphs up to polylogarithmic factors (Theorem 8.2), which yields polynomial-size non-deterministic weak refutations of smoothed $k$-CSPs with $\tilde{O}(n^{k/2-(k-2)/(2(k+8))})$ constraints, $\tilde{O}(n^{1.4})$ for $k=3$ (Theorem 9.2). The $\ell=O(1)$ endpoint for semirandom instances is the [strong refutation of semirandom CSPs](semirandom-csp-strong-refutation.md).

## Depends on

- [Semirandom and smoothed CSP instances and strong refutation](semirandom-and-smoothed-csps.md)

## Proof depends on

None.

## Sources

- Venkatesan Guruswami, Pravesh K. Kothari, Peter Manohar, "Algorithms and Certificates for Boolean CSP Refutation: Smoothed is no harder than Random", *STOC 2022*, 2022, arXiv:2109.04415v2, https://arxiv.org/abs/2109.04415 (Theorem 7.4 and its proof in Section 7.1, Fact 7.5; Theorem 5.1; Theorem 1 and Theorem 1.5 with the examples after Theorem 1; Theorems 2, 3, 8.2 and 9.2 for the prose remarks).
