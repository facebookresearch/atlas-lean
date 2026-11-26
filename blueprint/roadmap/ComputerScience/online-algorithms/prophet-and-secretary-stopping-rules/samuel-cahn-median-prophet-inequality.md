# Samuel-Cahn's median-threshold prophet inequality and optimality of 1/2

Let $X_1, \dots, X_n$ be independent nonnegative random variables with countable support, observed in order; a gambler stopping at $i$ collects $X_i$ and collects $0$ if never stopping. Let $M = \max_i X_i$ (possibly with $\mathbb{E}[M] = \infty$).

1. (Threshold form) For a threshold $t \ge 0$, let $R$ be the probability that the rule "accept the first $X_i \ge t$" accepts nothing. If $2t \le \mathbb{E}[M]$ and $2R \ge 1$, or $\mathbb{E}[M] \le 2t$ and $2R \le 1$, the rule's expected reward is at least $\mathbb{E}[M]/2$; the same holds for strict thresholds.
2. (Samuel-Cahn) If $t$ is a median of $M$, accepting the first value $\ge t$ (when $t \ge \mathbb{E}[M]/2$) or $> t$ (when $t \le \mathbb{E}[M]/2$) guarantees $\mathbb{E}[M]/2$; hence some single-threshold rule always does.
3. (Tightness) For every $\varepsilon > 0$ there are two-variable instances on which every stopping rule, even one using the whole history, collects less than $(1/2 + \varepsilon)\,\mathbb{E}[M]$.

## Proof sketch

The reward is at least $t(1-R) + R\sum_i \mathbb{E}[(X_i - t)^+]$, since a value above $t$ is reached with probability at least $R$; and $\mathbb{E}[M] \le t + \sum_i \mathbb{E}[(X_i - t)^+]$. Under either sign condition the two bounds combine to $\mathbb{E}[M]/2$, and a median of $M$ makes $R$ straddle $1/2$. Tightness: $X_1 = 1$ and $X_2 = k+1$ with probability $1/(k+1)$, else $0$.

## Depends on

- [Prophet inequality with a single threshold](../../../Probability/martingales/prophet-inequalities/prophet-inequality-with-a-single-threshold.md)

## Proof depends on

- [Prophet inequality with a single threshold](../../../Probability/martingales/prophet-inequalities/prophet-inequality-with-a-single-threshold.md)

## Sources

- Ulrich Krengel and Louis Sucheston, "Semiamarts and Finite Values", Bulletin of the American Mathematical Society 83, 1977.
- Ester Samuel-Cahn, "Comparison of Threshold Stop Rules and Maximum for Independent Nonnegative Random Variables", The Annals of Probability 12(4), 1984.
- Robert Kleinberg and S. Matthew Weinberg, "Matroid Prophet Inequalities", Proceedings of the 44th ACM Symposium on Theory of Computing (STOC), 2012.
- Tim Roughgarden, "Twenty Lectures on Algorithmic Game Theory", Cambridge University Press, 2016.
