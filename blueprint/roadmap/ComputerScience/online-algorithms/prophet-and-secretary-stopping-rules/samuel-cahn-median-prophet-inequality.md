# Samuel-Cahn's median-threshold prophet inequality and optimality of 1/2

Let $X_1, \dots, X_n$ be independent nonnegative random variables, observed in order; a gambler stopping at $i$ collects $X_i$ and collects $0$ if never stopping. Let $M = \max_i X_i$ (possibly with $\mathbb{E}[M] = \infty$).

1. (Threshold form) Suppose $\mathbb{E}[M] < \infty$. For a threshold $t \ge 0$, let $R = \Pr[M \le t]$ be the probability that the rule "accept the first $X_i > t$" accepts nothing. The rule's expected reward is at least $t + R(\mathbb{E}[M] - 2t)$; in particular it is at least $\mathbb{E}[M]/2$ when $t = \mathbb{E}[M]/2$, and also whenever $R = 1/2$.
2. (Samuel-Cahn) Let $m$ be a median of $M$, that is, $\Pr[M < m] \le 1/2$ and $\Pr[M > m] \le 1/2$, and let $\beta = \sum_i \mathbb{E}[(X_i - m)^+]$. If $\beta \ge m$, the rule "accept the first $X_i > m$" has expected reward at least $\mathbb{E}[M]/2$; if $\beta \le m$, the rule "accept the first $X_i \ge m$" does. Hence some single-threshold rule always guarantees $\mathbb{E}[M]/2$.
3. (Tightness) For every $\varepsilon > 0$ there are two-variable instances on which every stopping rule, even one using the whole history, collects less than $(1/2 + \varepsilon)\,\mathbb{E}[M]$.

## Proof sketch

For a threshold $c$, let $p$ be the probability that the rule accepts. It collects more than $c$ (at least $c$ for a non-strict threshold) with probability $p$, and it reaches each index with no earlier acceptance with probability at least $1 - p$, so its reward is at least $cp + (1 - p)\sum_i \mathbb{E}[(X_i - c)^+]$; also $\mathbb{E}[M] \le c + \sum_i \mathbb{E}[(X_i - c)^+]$. For item 1 take $c = t$ and $p = 1 - R$. Since $t + R(\mathbb{E}[M] - 2t) - \mathbb{E}[M]/2 = (2t - \mathbb{E}[M])(1 - 2R)/2$, the bound reaches $\mathbb{E}[M]/2$ exactly when $2t \le \mathbb{E}[M]$ and $2R \ge 1$, or $\mathbb{E}[M] \le 2t$ and $2R \le 1$. For item 2 take $c = m$, so $\mathbb{E}[M] \le m + \beta$ and the reward is at least $mp + (1 - p)\beta$, which exceeds $(m + \beta)/2$ by $(p - 1/2)(m - \beta)$: for the strict rule $p = \Pr[M > m] \le 1/2$, and for the non-strict rule $p = \Pr[M \ge m] \ge 1/2$. Tightness: $X_1 = 1$ and $X_2 = k+1$ with probability $1/(k+1)$, else $0$.

## Depends on

- [Prophet inequality with a single threshold](../../../Probability/martingales/prophet-inequalities/prophet-inequality-with-a-single-threshold.md)

## Sources

- Ulrich Krengel and Louis Sucheston, "Semiamarts and Finite Values", Bulletin of the American Mathematical Society 83, 1977.
- Ester Samuel-Cahn, "Comparison of Threshold Stop Rules and Maximum for Independent Nonnegative Random Variables", The Annals of Probability 12(4), 1984: p. 1213 (the rules $t(c)$, $s(c)$ and the tightness example) and p. 1214, (1.2) and Theorem 1.
- Robert Kleinberg and S. Matthew Weinberg, "Matroid Prophet Inequalities", Proceedings of the 44th ACM Symposium on Theory of Computing (STOC), 2012.
- Tim Roughgarden, "Twenty Lectures on Algorithmic Game Theory", Cambridge University Press, 2016.
- J. Correa, P. Foncea, R. Hoeksma, T. Oosterwijk and T. Vredeveld, "Recent Developments in Prophet Inequalities", ACM SIGecom Exchanges 17(1), 2018, §2, pp. 63-64: the bound $\mathbb{E}(X_r) \ge pT + (1 - p)(\mathbb{E}(\hat X) - T)$ for the first value above $T$, the two choices of $T$, and the two-variable tightness example. <https://www.sigecom.org/exchanges/volume_17/1/CORREA.pdf>
- T. Roughgarden, CS364A Algorithmic Game Theory, Lecture #6 "Simple Near-Optimal Auctions", Stanford University, 2013, Theorem 2.1 and (4)-(5), for the threshold rule accepting the first prize $\ge t$. <https://theory.stanford.edu/~tim/f13/l/l6.pdf>
