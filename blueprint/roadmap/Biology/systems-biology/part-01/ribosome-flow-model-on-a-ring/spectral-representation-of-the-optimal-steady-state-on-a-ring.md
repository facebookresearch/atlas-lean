# Spectral representation of the optimal steady state of the ribosome flow model on a ring

**Model.** The ribosome flow model on a ring (RFMR) describes ribosome flow along a circularised mRNA of $n > 2$ sites with occupancies $x_i\in[0,1]$ and rates $\lambda_1,\dots,\lambda_n > 0$, indices modulo $n$:

$$\dot x_i = \lambda_{i-1}x_{i-1}(1 - x_i) - \lambda_ix_i(1 - x_{i+1}),\qquad i = 1,\dots,n,$$

so ribosomes leaving site $n$ re-enter site $1$ (perfect recycling). The total density $H(x) = x_1 + \dots + x_n$ is a first integral. For each $s\in(0,n)$ the level set $\{x\in[0,1]^n : H(x) = s\}$ contains a unique steady state $e(s)$ attracting all trajectories in it, with production rate $R(s)$ satisfying $\lambda_ie_i(1 - e_{i+1}) = R(s)$ for all $i$. $R$ is positively homogeneous of degree one in the rates, and there is a unique total density $s^\ast$ maximising $R(s)$; write $R^\ast = R(s^\ast)$ and $e^\ast = e(s^\ast)$.

**Theorem.** Let $A$ be the $n\times n$ periodic Jacobi matrix with zero diagonal, $A_{i,i+1} = A_{i+1,i} = \lambda_i^{-1/2}$ ($i = 1,\dots,n$, indices modulo $n$). It is symmetric, non-negative and irreducible; let $\sigma > 0$ be its Perron eigenvalue and $\zeta\in\mathbb{R}^n_{>0}$ a Perron eigenvector. Then

$$R^\ast = \sigma^{-2},\qquad e_i^\ast = \lambda_i^{-1/2}\sigma^{-1}\frac{\zeta_{i+1}}{\zeta_i}\quad(i = 1,\dots,n),\qquad s^\ast = \sigma^{-1}\sum_{i=1}^n\lambda_i^{-1/2}\frac{\zeta_{i+1}}{\zeta_i}.$$

**Consequences.**

- $R^\ast$ is a concave function of $(\lambda_1,\dots,\lambda_n)$, so maximising $R^\ast$ under an affine bound on the rates is a convex problem, and $\partial R^\ast/\partial\lambda_i > 0$. Being positively homogeneous of degree one, $R^\ast$ is affine along every ray from the origin and hence not strictly concave; the source calls it strictly concave, which can hold at most on hyperplanes not containing the origin, such as $\sum_i\lambda_i = 1$.
- Cyclic shifts of the rates conjugate $A$ by a permutation matrix and leave $R^\ast, e^\ast, s^\ast$ unchanged (up to the shift).
- Homogeneous rates $\lambda_i\equiv\lambda_c$: $\sigma = 2\lambda_c^{-1/2}$, $\zeta = \mathbf{1}$, hence $R^\ast = \lambda_c/4$ and $e_i^\ast = 1/2$.
- Letting $\lambda_n\to\infty$, $A$ tends to the tridiagonal matrix of an open-chain ribosome flow model with $n-2$ sites and rates $\lambda_1,\dots,\lambda_{n-1}$; the optimal RFMR steady state then yields the open-chain steady state, so the open model is an RFMR initialised at its optimal total density.

## Depends on

- [Optimal total density of the ribosome flow model on a ring](../optimal-ribosome-density-in-ribosome-flow-models/optimal-total-density-of-the-ribosome-flow-model-on-a-ring.md)

## Expansion

The formulas satisfy the steady-state flow equations directly. Row $i+1$ of $A\zeta = \sigma\zeta$ reads $\lambda_i^{-1/2}\zeta_i + \lambda_{i+1}^{-1/2}\zeta_{i+2} = \sigma\zeta_{i+1}$, so $1 - e^\ast_{i+1} = \lambda_i^{-1/2}\zeta_i/(\sigma\zeta_{i+1})$ and therefore $\lambda_ie^\ast_i(1 - e^\ast_{i+1}) = \sigma^{-2}$ for every $i$. Positivity of the Perron vector keeps every $e^\ast_i$ in $(0,1)$, and the proof shows that the optimal total density corresponds to this positive eigenvector. Monotonicity in the rates follows because raising $\lambda_i$ lowers an entry of the irreducible non-negative matrix $A$, which strictly lowers $\sigma$. Example: rates $(0.7, 1.6, 2.2)$ give $\sigma\approx 1.7940$, hence $R^\ast\approx 0.3107$ and $s^\ast\approx 1.4948$.

## Sources

- Y. Zarai, A. Ovseevich, M. Margaliot, *Optimal translation along a circular mRNA*, Scientific Reports 7 (2017), 9464, Introduction (Eqs. 4–6), "Spectral representation" (Eq. 8, Theorem 1, Eq. 9, Examples 2–3) and Corollary 1. <https://doi.org/10.1038/s41598-017-09602-6> (PMCID: PMC5573536)
