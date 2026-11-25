# McNemar's test with a random number of discordant pairs

Let $\mu$ be a probability measure and $X$, $Y$ measurable natural-valued random variables counting
the discordant pairs of the two types. Suppose that for every $N$ with $\mu(X + Y = N) > 0$, the
count $X$ has the law $\mathrm{Bin}(N, 1/2)$ under $\mu$ conditioned on the event $\{X + Y = N\}$.
Then the [McNemar p-value](mcnemar-pvalue.md) at the observed number of discordant pairs,
$P(\omega) = \Pr[\mathrm{Bin}(X(\omega) + Y(\omega), 1/2) \ge X(\omega)]$, is
[valid](../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md)
under $\mu$: $\mu(P \le t) \le t$ for every $t \in [0, 1]$.

The conditional binomial law is a hypothesis. Under the
[equal-rate Poisson null](is-valid-pvalue-mcnemar-pvalue-total.md) the p-value is valid without it.
In the model with a fixed number of pairs and multinomial cell counts, the conditional law has to be
supplied as this hypothesis.
