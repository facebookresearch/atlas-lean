# Limit of complex balanced distributions under fast-degradation scaling

Let $(\mathcal N, \lambda)$ be a stochastic reaction network with a proper subset $\mathcal U = \{U_1, \dots, U_m\}$ of species and projection $\rho(x) \in \mathbb N_0^m$ onto the $\mathcal U$-coordinates. For $\beta \in \mathbb R^m_{>0}$ and $N \in \mathbb N$ scale the kinetics as

$$\lambda^\beta_{N, y \to y'} = N^{\langle \beta, \rho(y) \rangle}\,\lambda_{y \to y'},$$

so that reactions consuming species of $\mathcal U$ are accelerated by a power of $N$.

**Proposition.** If $\pi$ is a complex balanced distribution for $(\mathcal N, \lambda)$ on an irreducible component $\Gamma$, then

$$\pi^\beta_N(x) = \frac{N^{-\langle \beta, \rho(x) \rangle}\pi(x)}{\sum_{x' \in \Gamma} N^{-\langle \beta, \rho(x') \rangle}\pi(x')}$$

is a complex balanced distribution for $(\mathcal N, \lambda^\beta_N)$ on $\Gamma$.

**Theorem.** Let $\gamma^\beta_0 = \min\{\langle \beta, \rho(x) \rangle : x \in \Gamma\}$ and $\Gamma^\beta_0 = \{x \in \Gamma : \langle \beta, \rho(x)\rangle = \gamma^\beta_0\}$. Then for every $x \in \Gamma$,

$$\lim_{N \to \infty} \pi^\beta_N(x) = \begin{cases} \pi(x)/\pi(\Gamma^\beta_0), & x \in \Gamma^\beta_0, \\ 0, & x \in \Gamma \setminus \Gamma^\beta_0. \end{cases}$$

**Theorem (identification with the reduced network).** Let $(\mathcal N, \lambda)$ be weakly reversible, $\mathcal U$ a set of [non-interacting species](conditional-stationary-distribution-after-eliminating-non-interacting-species.md), $\pi$ complex balanced on $\Gamma$ with $\Gamma_0 = \{\rho = 0\} \cap \Gamma \neq \emptyset$, and suppose that $\mathcal U$ satisfies the elimination order condition, or consists of intermediates, or that $\mathcal N$ is reversible. Then $\lim_{N\to\infty}\pi^\beta_N$ is a stationary distribution (or a linear combination of stationary distributions on disjoint irreducible components) of the reduced network $(\mathcal N_{\mathcal U}, \lambda_{\mathcal U})$, supported on $\Gamma_0$.

## Depends on

- [Conditional stationary distribution after eliminating non-interacting species](conditional-stationary-distribution-after-eliminating-non-interacting-species.md)
- [Complex-balanced concentrations](../../complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md)

## Expansion

The complex balance equations are invariant under the reweighting $\pi \mapsto N^{-\langle\beta,\rho\rangle}\pi$ combined with the rate scaling, because $\rho$ is linear and each reaction out of complex $y$ picks up the factor $N^{\langle\beta,\rho(y)\rangle}$ exactly compensating the shift of the weight; the mass-action assumption is not needed. As $N \to \infty$ the reweighting concentrates on the states minimizing $\langle\beta,\rho\rangle$, which for non-interacting species is $\{\rho = 0\}$, and the limit is the conditional law studied in the elimination theorem. Thus the multiscale limit and algebraic elimination agree under the stated sufficient conditions, although in general the two can differ.

## Sources

- L. Hoessly, C. Wiuf and P. Xia, "Asymptotic analysis for stationary distributions of multiscaled reaction networks", *Advances in Applied Probability* 58(3) (2025), 887–917, Proposition 4.1 and Theorems 4.2 and 4.3, <https://doi.org/10.1017/apr.2025.10040> (preprint arXiv:2402.02276).