# Event-level pure differential privacy

For a family $M(d)$ of probability mass functions on outputs, a relation $\mathrm{adj}$ on databases and $\varepsilon \in \mathbb{R}$, $M$ is event-level $\varepsilon$-differentially private when $\varepsilon \ge 0$ and, for every ordered pair with $\mathrm{adj}(d, d')$ and every set $S$ of outputs,

$$
M(d)(S) \le e^{\varepsilon} \, M(d')(S),
$$

where $M(d)(S) = \sum_{o \in S} M(d)(o)$ is the outer-measure mass of $S$. Every subset of outputs counts as an event; no measurable structure is used.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Section 2.3, Definition 2.4 with $\delta = 0$.
