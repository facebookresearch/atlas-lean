# Statement of the Kolmogorov distance via left-continuous distribution functions

This is
the proposition that for every probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance
$1$ and finite third absolute moment and every integer $n \ge 1$, if $S_n = X_1 + \dots + X_n$ for
independent random variables $X_1, X_2, \dots$ each with law $\mu$, then

$$
\sup_{x \in \mathbb{R}} \bigl|P(S_n/\sqrt{n} < x) - \Phi(x)\bigr|
= \sup_{x \in \mathbb{R}} \bigl|P(S_n/\sqrt{n} \le x) - \Phi(x)\bigr|,
$$

where $\Phi$ is the standard normal distribution function.

## Sources

- the right-CDF catalogue definition and retained Shevtsova2011 lines 104-108, which explicitly use a left-continuous CDF. This probability bridge is requested, not inferred by replacing strict with non-strict events.
