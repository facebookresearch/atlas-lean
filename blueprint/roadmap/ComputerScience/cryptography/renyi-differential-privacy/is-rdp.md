# Rényi differential privacy

Let $M$ assign to each database a probability mass function on a finite type of outputs, let $\mathrm{adj}$ be a relation on databases and $\alpha, \varepsilon \in \mathbb{R}$. The mechanism is $(\alpha, \varepsilon)$-Rényi differentially private when $\varepsilon \ge 0$, $\alpha > 1$, and for every ordered pair with $\mathrm{adj}(d, d')$, $M(d)$ has [support inside](support.md) that of $M(d')$ and the [Rényi divergence](renyi-div.md) satisfies

$$
D_\alpha\big(M(d) \,\|\, M(d')\big) \le \varepsilon .
$$

## Sources

- I. Mironov, *Rényi Differential Privacy*, IEEE Computer Security Foundations Symposium (CSF), 2017.
