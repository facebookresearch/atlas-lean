# Probability of a Fisher–Yates outcome

Let $x$ be a vector of length $n$, and consider the
draw histories $d$, which assign to each position $i < n$ a number $d_i$ with $0 \le d_i < n - i$.
For every outcome $o$ (a vector of length $n$ together with a cost pair), the probability that
the Fisher–Yates output distribution of $x$ assigns to $o$ equals the sum, over all draw histories
$d$ for which the Fisher–Yates computation on $x$ and $d$ yields exactly $o$, of
$\prod_{i=0}^{n-1} \frac{1}{n - i}$.

Distinct histories that yield the same outcome (for example when values of $x$ repeat) add up,
and an outcome that no history yields has probability $0$.
