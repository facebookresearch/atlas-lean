# Upper bound on the total Beta-coalescent rate

For the Beta$(2-\alpha,\alpha)$-coalescent with $\alpha \in (0,2)$, the merger rates are

$$\lambda_{b,k} = \frac{B(k-\alpha,\ \alpha+b-k)}{B(2-\alpha,\ \alpha)}, \qquad 2 \le k \le b,$$

and the total coalescent rate with $b \ge 2$ lineages is $\lambda_b = \sum_{k=2}^{b}\binom{b}{k}\lambda_{b,k}$. Then

$$\lambda_b \le (b-1)\left(\frac{b}{2}\right)^{\alpha-1}.$$

At $\alpha = 2$ (the Kingman limit) the right-hand side equals $\binom{b}{2}$; numerically, the bound is a close approximation for $\alpha \in [1,2)$, so that

$$\log \lambda_b \approx (\alpha - 1)\log(b/2) + \log(b-1),$$

showing that smaller $\alpha$ gives smaller total rates and hence longer branches than Kingman's coalescent.

## Depends on

- [Closed form of the Beta-coalescent rates](../multiple-merger-coalescents/merger-rates-and-beta-coalescents/merger-rate-beta-lambda.md)

## Expansion

Writing $\binom{b}{k}\lambda_{b,k}$ in Gamma functions and using $\Gamma(2-\alpha)\Gamma(\alpha) = (1-\alpha)\pi/\sin((1-\alpha)\pi) \ge 1$, two applications of Wendel's inequality for ratios $\Gamma(x+s)/\Gamma(x+1)$ bound each term by $b \cdot \frac{1}{k(k-1)} \cdot \left(\frac{b}{k-1} - 1\right)^{\alpha-1}$, which is at most $\frac{b}{k(k-1)}(b/2)^{\alpha-1}$. Summing the telescoping series $\sum_{k=2}^{b} \frac{1}{k(k-1)} = \frac{b-1}{b}$ gives the bound. The source carries out the main case explicitly and states that a similar argument covers the remaining range of $\alpha$.

## Sources

- J. Zhang and J. A. Palacios, "Multiple merger coalescent inference of effective population size", *Philosophical Transactions of the Royal Society B* (2025), Eq. (2.5) and Appendix A.1, Proposition 1 and Eqs. (A1)–(A3). <https://doi.org/10.1098/rstb.2023.0306> (PMC11867189)
