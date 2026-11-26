# Bribing O(n/log n) voters biases a monotone election

Let $f : \{-1,1\}^n \to \{-1,1\}$ be monotone, $n \ge 2$, and $0 \le a < 1$. If $\mathbb{E}[f] \ge -a$, then there is a coalition $J$ with

$$|J| \le \frac{8 a n}{(1 - a^2)\ln n} + 1$$

such that fixing all voters in $J$ to $1$ makes $\mathbb{E}[f] \ge a$; symmetrically with $-1$. Moreover, if $\mathrm{Var}[f] \ge \delta > 0$ and $0 < \varepsilon \le 1$, a coalition of size $O\big(n \log(2/(\varepsilon\delta))/\log n\big)$ can force $\mathbb{E}[f] \ge 1 - \varepsilon$, and some coalition of that size has coalitional influence at least $1 - \varepsilon$.

## Proof sketch

Bribe greedily the most influential voter: for monotone $f$, fixing voter $i$ to $1$ raises the mean by $\mathbf{Inf}_i[f]$, and by KKL some voter has influence at least $\mathrm{Var}[f]\ln n/(4n)$; while the mean stays in $[-a, a]$ the variance is at least $1 - a^2$, so $O(an/((1 - a^2)\log n))$ steps suffice. For near-unanimity, run a two-phase geometric argument on the distance to $\pm 1$.

## Depends on

- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)
- [Variance on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-variance.md)
- [Coalitional influence](coalitional-influence.md)

## Proof depends on

- [Kahn–Kalai–Linial inequality](../kahn-kalai-linial-inequality/the-kkl-inequality-statement-and-elementary-boun/kkl-inequality-max.md)
- [A direction is unate exactly when its influence equals its degree-one coefficient](unate-direction-influence-equals-coefficient.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- J. Kahn, G. Kalai and N. Linial, "The Influence of Variables on Boolean Functions", FOCS 1988.
