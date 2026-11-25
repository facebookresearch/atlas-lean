# Pure differential privacy for discrete mechanisms

Let $M$ assign to each database $d$ a probability mass function $M(d)$ on a type of outputs, let $\mathrm{adj}$ be a relation on databases and let $\varepsilon \in \mathbb{R}$. The mechanism $M$ is $\varepsilon$-differentially private for $\mathrm{adj}$ when $\varepsilon \ge 0$ and, for every ordered pair with $\mathrm{adj}(d, d')$ and every output $o$,

$$
M(d)(o) \le e^{\varepsilon} \, M(d')(o),
$$

as an inequality of extended nonnegative reals. The bound is only required in the order given by $\mathrm{adj}$; for a symmetric relation it holds in both directions.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Section 2.3, Definition 2.4 with $\delta = 0$.
