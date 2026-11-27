# Adaptive composition of Rényi differential privacy

Let $A$ and $B$ be finite types. Let $M_1$ be [$(\alpha, \varepsilon_1)$-Rényi differentially private](is-rdp.md) for $\mathrm{adj}$ with outputs in $A$, let $\varepsilon_2 \ge 0$, and for every $y \in A$ let $d \mapsto M_2(d, y)$ be $(\alpha, \varepsilon_2)$-Rényi differentially private for $\mathrm{adj}$ with outputs in $B$. Then the mechanism that draws $y \sim M_1(d)$, then $z \sim M_2(d, y)$, and releases $(y, z)$ is $(\alpha, \varepsilon_1 + \varepsilon_2)$-Rényi differentially private for $\mathrm{adj}$.

## Sources

- I. Mironov, *Rényi Differential Privacy*, IEEE Computer Security Foundations Symposium (CSF), 2017, Proposition 1.
