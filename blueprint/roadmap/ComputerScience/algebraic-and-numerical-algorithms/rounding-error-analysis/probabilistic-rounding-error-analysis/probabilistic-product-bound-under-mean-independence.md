# Probabilistic product bound under mean independence

Let $u \in (0, 1)$, let $\delta_1, \dots, \delta_n$ be random variables of mean zero with $|\delta_k| \le u$ and $\mathbb{E}[\delta_{k+1} \mid \delta_1, \dots, \delta_k] = 0$ for $k = 1, \dots, n - 1$, and let $\rho_i \in \{1, -1\}$. Then for every $\lambda > 0$,

$$\prod_{i=1}^n (1 + \delta_i)^{\rho_i} = 1 + \theta_n, \qquad |\theta_n| \le \exp\Big(\frac{\lambda\sqrt n\,u + n u^2}{1 - u}\Big) - 1,$$

with probability at least $1 - 2\exp(-\lambda^2/2)$. The partial sums $E_k = \sum_{i \le k} \rho_i \delta_i$ form a martingale with increments bounded by $u$, so the Azuma–Hoeffding inequality gives $|E_n| \le \lambda\sqrt n\,u$ with that probability, and $\log(1 + \delta_i)$ lies between $\delta_i \mp \delta_i^2/(1 - u)$. Unlike the deterministic bound $|\theta_n| \le \gamma_n$, this needs no condition $nu < 1$.

Independent errors of mean zero, as in the [probabilistic model of rounding errors](probabilistic-model-of-rounding-errors.md), satisfy the hypothesis. Writing $\lambda = (1 - u)\lambda'$ turns the bound into the form used for that model: for every $\lambda' > 0$, $|\theta_n| \le \tilde\gamma_n(\lambda')$ with probability at least $P(\lambda')$, where

$$\tilde\gamma_n(\lambda') = \exp\Big(\lambda'\sqrt{n}\,u + \frac{n u^2}{1 - u}\Big) - 1 = \lambda'\sqrt n\,u + O(u^2), \qquad P(\lambda') = 1 - 2\exp\Big(-\frac{\lambda'^2 (1 - u)^2}{2}\Big).$$

Since [stochastic rounding errors are mean independent](stochastic-rounding-errors-are-mean-independent.md), the bound also holds for stochastic rounding with $u$ replaced by $2u$, provided $2u < 1$ and every rounded result satisfies $|\delta| \le 2u$, as it does with unbounded exponents or when no result underflows or overflows; no further modelling assumption is needed.

## Depends on

- [Probabilistic model of rounding errors](probabilistic-model-of-rounding-errors.md)
- [Stochastic rounding](stochastic-rounding.md)

## Proof depends on

- [Azuma's inequality](../../../../Probability/concentration-inequalities/azuma-inequality.md)
- [Stochastic rounding errors are mean independent](stochastic-rounding-errors-are-mean-independent.md)

## Related topics

- [The constant γₙ of rounding error analysis](../gamma.md)

## Sources

- M. P. Connolly, N. J. Higham and T. Mary, "Stochastic rounding and its probabilistic backward error analysis", *SIAM J. Sci. Comput.* 43(1):A566–A585, 2021; MIMS EPrint 2020.12, Section 4.2, Definition 4.6 (martingale), Lemma 4.7 (Azuma–Hoeffding inequality), the constant (4.2), Theorem 4.8 with its proof, and the change of parameter $\lambda = (1 - u)\lambda'$ relating it to the independent case. <https://eprints.maths.manchester.ac.uk/2763/1/paper.pdf>
- N. J. Higham and T. Mary, "A new approach to probabilistic rounding error analysis", *SIAM J. Sci. Comput.* 41(5):A2815–A2835, 2019; MIMS EPrint 2018.33, Section 2, Lemma 2.2, Lemma 2.3 (Hoeffding's inequality), the constant (2.1), and Theorem 2.4 with its proof and the probability (2.3), the version for independent errors proved with Hoeffding's inequality, whose constant and probability are those of the specialization above. <https://eprints.maths.manchester.ac.uk/2673/1/paper.pdf>
