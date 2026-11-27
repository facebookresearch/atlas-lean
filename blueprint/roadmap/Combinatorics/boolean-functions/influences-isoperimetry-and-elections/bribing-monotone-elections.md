# Bribing O(n/log n) voters biases a monotone election

Let $f : \{-1,1\}^n \to \{-1,1\}$ be monotone, $n \ge 2$, and $0 \le a < 1$. If $\mathbb{E}[f] \ge -a$, then there is a coalition $J$ with

$$|J| \le \frac{8 a n}{(1 - a^2)\ln n} + 1$$

such that fixing all voters in $J$ to $1$ makes $\mathbb{E}[f] \ge a$; symmetrically with $-1$. Moreover, if $\mathrm{Var}[f] \ge \delta > 0$ and $0 < \varepsilon \le 1$, a coalition of size $O\big(n \log(2/(\varepsilon\delta))/\log n\big)$ can force $\mathbb{E}[f] \ge 1 - \varepsilon$, and some coalition of that size has coalitional influence at least $1 - \varepsilon$.

## Proof sketch

Bribe greedily a most influential voter, keeping bribed voters as dummy coordinates so that every intermediate function lives on all $n$ coordinates; for monotone $f$, fixing voter $i$ to $1$ raises the mean by $\mathbf{Inf}_i[f]$. Every nonconstant such function has a coordinate of influence at least $\mathrm{Var}[f]\ln n/(4n)$: if $\tilde{\mathbf I} = \mathbf{I}[f]/\mathrm{Var}[f] \ge \ln(n)/4$ the average influence already gives this, and otherwise the KKL edge-isoperimetric theorem gives an influence at least $9\tilde{\mathbf I}^{-2}9^{-\tilde{\mathbf I}} > 144\,n^{-\ln(9)/4}/\ln^2 n$, which is at least $\ln n/(4n)$ for every $n \ge 2$. While the mean lies in $[-a, a)$ the variance is at least $1 - a^2$, so each bribe raises the mean by at least $(1 - a^2)\ln n/(4n)$, and starting from a mean of at least $-a$ at most $8an/((1 - a^2)\ln n) + 1$ bribes reach a mean of at least $a$. For near-unanimity (O'Donnell, Ex. 9.27) count the bribes that move the mean past each interval $[1 - 2\eta, 1 - \eta]$, on which the variance is at least $\eta$; for monotone $f$ the union of a coalition bribed to $1$ and one bribed to $-1$ has coalitional influence at least $1 - \varepsilon$.

## Depends on

- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)
- [Variance on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-variance.md)
- [Coalitional influence](coalitional-influence.md)

## Proof depends on

- [KKL edge-isoperimetric theorem](kkl-edge-isoperimetric-theorem.md)
- [A direction is unate exactly when its influence equals the absolute value of its degree-one coefficient](unate-direction-influence-equals-coefficient.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- J. Kahn, G. Kalai and N. Linial, "The Influence of Variables on Boolean Functions", FOCS 1988.
