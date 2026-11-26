# Probabilistic bound for products of rounding errors

Let $u \in (0, 1)$, let $\delta_1, \dots, \delta_n$ be independent random variables of mean zero with $|\delta_i| \le u$, and let $\rho_i \in \{1, -1\}$. For $\lambda > 0$ let

$$\tilde\gamma_n(\lambda) = \exp\Big(\lambda\sqrt{n}\,u + \frac{n u^2}{1 - u}\Big) - 1 = \lambda\sqrt n\,u + O(u^2).$$

Then $\prod_{i=1}^n (1 + \delta_i)^{\rho_i} = 1 + \tilde\theta_n$ with $|\tilde\theta_n| \le \tilde\gamma_n(\lambda)$, with probability at least

$$P(\lambda) = 1 - 2\exp\Big(-\frac{\lambda^2 (1 - u)^2}{2}\Big).$$

Unlike the deterministic bound $|\theta_n| \le \gamma_n$, this needs no condition $nu < 1$. The proof takes logarithms, bounds $\log(1 + \delta_i)$ between $\delta_i \mp \delta_i^2/(1 - u)$, and applies Hoeffding's inequality to $\sum_i \rho_i \delta_i$.

## Depends on

- [Probabilistic model of rounding errors](probabilistic-model-of-rounding-errors.md)

## Proof depends on

- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)

## Related topics

- [The constant γₙ of rounding error analysis](../gamma.md)

## Sources

- N. J. Higham and T. Mary, "A new approach to probabilistic rounding error analysis", *SIAM J. Sci. Comput.* 41(5):A2815–A2835, 2019; MIMS EPrint 2018.33, Section 2, Lemma 2.2, Lemma 2.3 (Hoeffding's inequality), the constant (2.1), and Theorem 2.4 with its proof and the probability (2.3). <https://eprints.maths.manchester.ac.uk/2673/1/paper.pdf>
