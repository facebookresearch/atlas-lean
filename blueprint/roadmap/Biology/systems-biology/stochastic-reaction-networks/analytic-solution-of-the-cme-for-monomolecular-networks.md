# Exact solution of the chemical master equation for monomolecular networks

Consider a monomolecular reaction network on species $S_1, \dots, S_n$, with conversions $S_j \to S_k$ at rate $c_{jk}(t)$, inflows $\emptyset \to S_k$ at rate $c_{0k}(t)$ and degradations $S_k \to \emptyset$ at rate $c_{k0}(t)$, and let $A(t)$, $b(t)$ be the matrix and vector of the linear reaction-rate equations $\dot x = A(t)x + b(t)$ (Vastola 2021, Eqs. (18)–(20)). Let $\lambda$ solve $\dot\lambda = A(t)\lambda + b(t)$, $\lambda(t_0) = 0$, and $w^{(k)}$ solve $\dot w^{(k)} = A(t)w^{(k)}$, $w^{(k)}(t_0) = \epsilon_k$. Theorem 1 of Jahnke and Huisinga (2007), restated as Theorem 2 of Vastola, states: if $P(x, t_0) = \delta(x - \xi)$ for some $\xi \in \mathbb{N}^n$, then the solution of the chemical master equation is

$$P(x, t) = \mathcal P(x, \lambda(t)) \star \mathcal M(x, \xi_1, w^{(1)}(t)) \star \cdots \star \mathcal M(x, \xi_n, w^{(n)}(t)),$$

the convolution of a product Poisson law with parameter $\lambda(t)$ and the laws $\mathcal M(x, \xi_k, w^{(k)}(t))$ of the first $n$ counts of a multinomial law with $\xi_k$ trials and the $n + 1$ cell probabilities $w^{(k)}_1(t), \dots, w^{(k)}_n(t)$ and $1 - \sum_{j=1}^{n} w^{(k)}_j(t)$ (Vastola 2021, Eq. (26)). The last cell, for molecules that have been degraded, is needed because $\sum_j w^{(k)}_j(t)$ can be less than one when particles can disappear; in particular $E[x_j(t)] = \sum_k \xi_k w^{(k)}_j(t) + \lambda_j(t)$.

## Expansion

1. The model: monomolecular reactions with time-dependent rates, the chemical master equation (18) and the reaction-rate equations (20)–(22).
2. Product Poisson laws, multinomial laws with a final cell for degraded molecules (only the first $n$ counts recorded), and their convolution, Eqs. (25)–(27) of the restating source.
3. The independent-particle interpretation: molecules present at time $t_0$ move independently between species and degradation, and inflowing molecules give a Poisson law; verification that the convolution solves the master equation, by Jahnke and Huisinga's direct argument or by the generating-function (Doi–Peliti) computation of the restating source.
4. Long-time behaviour: multinomial laws for closed systems and product Poisson laws for open ones, as separate statements to be fixed from Jahnke and Huisinga.

## Sources

- J. J. Vastola, Solving the chemical master equation for monomolecular reaction systems and beyond: a Doi–Peliti path integral view, J. Math. Biol. 83 (2021), article 48, Section 2.2, Eqs. (18)–(27) and Theorem 2. <https://doi.org/10.1007/s00285-021-01670-7>
- Original result: T. Jahnke and W. Huisinga, Solving the chemical master equation for monomolecular reaction systems analytically, J. Math. Biol. 54 (2007), 1–26 (published online 2006), Theorem 1. <https://doi.org/10.1007/s00285-006-0034-x> The formula follows Vastola, Theorem 2.
