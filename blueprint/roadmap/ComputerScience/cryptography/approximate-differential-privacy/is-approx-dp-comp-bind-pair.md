# Two-step adaptive composition of approximate differential privacy

Let $M$ be [$(\varepsilon_1, \delta_1)$-differentially private](is-approx-dp.md) for $\mathrm{adj}$, and let $K(a)$ be, for every first output $a$, a mechanism that is $(\varepsilon_2, \delta_2)$-differentially private for the same $\mathrm{adj}$, with $\varepsilon_2 \ge 0$ and $\delta_2 \ge 0$. Then the mechanism that draws $a \sim M(d)$, then $b \sim K(a)(d)$, and releases the pair $(a, b)$ is $(\varepsilon_1 + \varepsilon_2, \delta_1 + \delta_2)$-differentially private for $\mathrm{adj}$. The second budget is the same for every $a$.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Theorem 3.16 and Appendix B.
