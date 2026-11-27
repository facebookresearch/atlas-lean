# Probabilistic product bound under mean independence

Let $u \in (0, 1)$, let $\delta_1, \dots, \delta_n$ be random variables of mean zero with $|\delta_k| \le u$ and $\mathbb{E}[\delta_{k+1} \mid \delta_1, \dots, \delta_k] = 0$ for $k = 1, \dots, n - 1$, and let $\rho_i \in \{1, -1\}$. Then for every $\lambda > 0$,

$$\prod_{i=1}^n (1 + \delta_i)^{\rho_i} = 1 + \theta_n, \qquad |\theta_n| \le \exp\Big(\frac{\lambda\sqrt n\,u + n u^2}{1 - u}\Big) - 1,$$

with probability at least $1 - 2\exp(-\lambda^2/2)$. The partial sums $E_k = \sum_{i \le k} \rho_i \delta_i$ form a martingale with increments bounded by $u$, so the Azuma–Hoeffding inequality gives $|E_n| \le \lambda\sqrt n\,u$ with that probability. Since [stochastic rounding errors are mean independent](stochastic-rounding-errors-are-mean-independent.md), the bound holds for stochastic rounding with $u$ replaced by $2u$, provided $2u < 1$ and every rounded result satisfies $|\delta| \le 2u$, as it does with unbounded exponents or when no result underflows or overflows; no further modelling assumption is needed.

## Depends on

- [Stochastic rounding](stochastic-rounding.md)

## Proof depends on

- [Azuma's inequality](../../../../Probability/concentration-inequalities/azuma-inequality.md)
- [Stochastic rounding errors are mean independent](stochastic-rounding-errors-are-mean-independent.md)

## Related topics

- [Probabilistic bound for products of rounding errors](probabilistic-bound-for-products-of-rounding-errors.md): the version for independent errors.

## Sources

- M. P. Connolly, N. J. Higham and T. Mary, "Stochastic rounding and its probabilistic backward error analysis", *SIAM J. Sci. Comput.* 43(1):A566–A585, 2021; MIMS EPrint 2020.12, Section 4.2, Definition 4.6 (martingale), Lemma 4.7 (Azuma–Hoeffding inequality), the constant (4.2) and Theorem 4.8 with its proof. <https://eprints.maths.manchester.ac.uk/2763/1/paper.pdf>
