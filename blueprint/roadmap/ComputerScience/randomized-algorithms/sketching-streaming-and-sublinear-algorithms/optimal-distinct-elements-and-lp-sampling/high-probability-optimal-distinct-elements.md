# Optimal distinct elements with failure probability delta in O(eps^-2 log(1/delta) + log n) bits

For all $0 < \varepsilon, \delta < 1$ there is a one-pass randomized streaming algorithm solving the $(\varepsilon, \delta)$-distinct elements problem (output an estimate $\widetilde{F}_0$ of the number $F_0$ of distinct elements with $\Pr[\,|\widetilde{F}_0 - F_0| \le \varepsilon F_0\,] \ge 1 - \delta$) on insertion-only streams over $[n]$ with

$$
O\Big(\frac{\log(1/\delta)}{\varepsilon^{2}} + \log n\Big)
$$

bits of space. The same work solves *strong tracking*, where the estimate must be a $(1 \pm \varepsilon)$-approximation of the number of distinct elements seen so far simultaneously at every time of the stream, in $O\big(\varepsilon^{-2}(\log\log n + \log(1/\delta)) + \log n\big)$ bits, and proves an $\Omega(\varepsilon^{-2}\log\log n)$ lower bound for strong tracking with constant failure probability. Both upper bounds are optimal in the regime of the matching lower bounds, which for estimation is $\Omega(\varepsilon^{-2}\log(1/\delta) + \log n)$ for $\varepsilon$ and $\delta$ below an absolute constant and $n$ polynomially larger than $\varepsilon^{-2}\log(1/\delta)$. They are not optimal for every $\varepsilon$: for $\varepsilon < 1/n$ an exact $n$-bit bitmap of the elements seen so far answers every query, at every time, with fewer than $\varepsilon^{-2}$ bits.

## Proof sketch

Taking the median of $\log(1/\delta)$ independent copies multiplies the $\log n$ term, so the seeds are generated pseudorandomly instead. First, a constant-factor estimate valid at all times with probability $1 - \delta$ is obtained in $O(\log n + \log(1/\delta))$ bits from $\Theta(\log n + \log(1/\delta))$ Flajolet–Martin-type estimators built on pairwise independent hash functions whose seeds come from short random walks on expander graphs combined with averaging samplers; the estimators are split into groups, and each group is stored as its median plus small deviations, $O(1)$ bits per estimator on average. Second, $O(\log(1/\delta))$ copies of the Kane–Nelson–Woodruff algorithm share this constant-factor estimate, each using $O(\varepsilon^{-2})$ bits of state, with their $O(\log n)$-bit random seeds chosen along a walk on a constant-degree expander, so that a Chernoff bound for expander walks keeps the failure probability of the median at $\delta$; when $\varepsilon > (\log n)^{-1/4}$ the same pseudorandom grouping as in the first step is used instead, with $\Theta(\log n + \log(1/\delta))$ copies.

## Depends on

- [Turnstile streams, support size and linear sketches of a frequency vector](turnstile-streams-and-support-size.md)
- [Omega(eps^-2 log(1/delta)) lower bounds for distinct elements and Johnson-Lindenstrauss with failure probability delta](distinct-elements-lower-bound-with-failure-probability.md)

## Proof depends on

- [Chernoff bound for expander walks](../../../../GraphTheory/graph-families-and-operations/expander-graphs/chernoff-bound-expander-walk.md)
- [Kane-Nelson-Woodruff distinct-elements algorithm with O(1/eps^2 + log n) bits](optimal-space-distinct-elements-algorithm.md)

## Sources

- Jarosław Błasiok, "Optimal streaming and tracking distinct elements with high probability", SODA (2018); ACM Trans. Algorithms 16 (2020), arXiv:1804.01642, Theorems 4, 6 and 8.
