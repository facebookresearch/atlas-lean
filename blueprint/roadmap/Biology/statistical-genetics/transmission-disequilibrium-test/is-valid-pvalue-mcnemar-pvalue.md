# Validity of the one-sided McNemar test

Let the discordant counts $X$ and $Y$ be independent measurable Poisson counts with a common rate $a > 0$.
Conditionally on $X + Y = N$, the exact one-sided McNemar p-value $P$ of $X$ is valid:
$\Pr[P \le s \mid X + Y = N] \le s$ for every $s \in [0, 1]$. The bound holds for every common rate $a$.

The same theorem is the conditional TDT when $X$ and $Y$ are the transmitted and untransmitted counts,
modeled as independent Poisson counts with equal rates under the null.

## Sources

- McNemar (1947); Lehmann and Romano (2005), Section 4.6 and Lemma 3.3.1.
