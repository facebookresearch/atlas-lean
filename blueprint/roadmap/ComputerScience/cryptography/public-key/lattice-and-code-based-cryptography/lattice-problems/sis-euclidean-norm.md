# The short integer solution problem in the Euclidean norm

The Euclidean variant $\ell_2\text{-}\mathrm{SIS}_{n,m,q,\beta}$ asks, for a uniform $A \in \mathbb{Z}_q^{n \times m}$ and a real bound $\beta > 0$, for a nonzero $z \in \mathbb{Z}^m$ with $A z \equiv 0 \pmod q$ and $\|z\|_2 \le \beta$. The corresponding hardness assumption for a parameter family is that every probabilistic polynomial-time solver succeeds with negligible probability. Since $\|z\|_\infty \le \|z\|_2 \le \sqrt{m}\,\|z\|_\infty$, a solution with $\|z\|_2 \le \beta$ is an $\ell_\infty$ solution with bound $\lfloor \beta \rfloor$, and an $\ell_\infty$ solution with bound $\beta$ is an $\ell_2$ solution with bound $\sqrt m\,\beta$.

## Depends on

- [The short integer solution problem (SIS)](short-integer-solution-problem.md)

## Sources

- Daniele Micciancio and Oded Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing, 2007.
