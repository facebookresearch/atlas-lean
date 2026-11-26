# Approximate differential privacy for discrete mechanisms

Let $M$ assign to each database $d$ a probability mass function $M(d)$ on outputs, let $\mathrm{adj}$ be a relation on databases and let $\varepsilon, \delta \in \mathbb{R}$. The mechanism is $(\varepsilon, \delta)$-differentially private when $\varepsilon \ge 0$, $\delta \ge 0$ and, for every ordered pair with $\mathrm{adj}(d, d')$ and every set $S$ of outputs,

$$
M(d)(S) \le e^{\varepsilon} \, M(d')(S) + \delta,
$$

in the extended nonnegative reals, with $M(d)(S) = \sum_{o \in S} M(d)(o)$. Every subset of outputs is an event, and $\delta$ may exceed $1$.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Definition 2.4.
