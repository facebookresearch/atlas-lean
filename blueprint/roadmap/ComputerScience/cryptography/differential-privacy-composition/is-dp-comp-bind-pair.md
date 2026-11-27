# Two-step adaptive composition of pure differential privacy

Let $M$ be [$\varepsilon_1$-differentially private](../differential-privacy/is-dp.md) for $\mathrm{adj}$ and let $K(a)$ be, for every first output $a$, an $\varepsilon_2$-differentially private mechanism for the same $\mathrm{adj}$, with $\varepsilon_2 \ge 0$. Then the mechanism that draws $a \sim M(d)$, then $b \sim K(a)(d)$, and releases the pair $(a, b)$ is $(\varepsilon_1 + \varepsilon_2)$-differentially private for $\mathrm{adj}$.
