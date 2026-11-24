# McNemar's test under the equal-rate Poisson null

Let $X$ and $Y$ be measurable natural-valued random variables that are independent under a measure
$\mu$, each with the Poisson law of the same rate $r \ge 0$ (the Poisson null of marginal
homogeneity); in particular $\mu$ is a probability measure. Then the
[McNemar p-value](mcnemar-pvalue.md) at the observed number of discordant pairs,
$P(\omega) = \Pr[\mathrm{Bin}(X(\omega) + Y(\omega), 1/2) \ge X(\omega)]$, is
[valid](../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md)
under $\mu$, for every rate $r \ge 0$, including $r = 0$: $\mu(P \le t) \le t$ for every
$t \in [0, 1]$.

With $X$ and $Y$ the transmitted and untransmitted counts, modeled as independent Poisson counts
with equal rates, this is the TDT at the observed total. That is a statistical model of the counts,
not a consequence of Mendelian segregation.
