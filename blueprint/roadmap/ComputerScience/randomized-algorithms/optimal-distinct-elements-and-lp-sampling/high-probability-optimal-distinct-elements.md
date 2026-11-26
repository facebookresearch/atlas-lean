# Optimal distinct elements with failure probability delta in O(eps^-2 log(1/delta) + log n) bits

For all $0 < \varepsilon, \delta < 1$ there is a one-pass randomized streaming algorithm solving the $(\varepsilon, \delta)$-distinct elements problem (output an estimate $\widetilde{F}_0$ of the number $F_0$ of distinct elements with $\Pr[\,|\widetilde{F}_0 - F_0| \le \varepsilon F_0\,] \ge 1 - \delta$) on insertion-only streams over $[n]$ with

$$
O\Big(\frac{\log(1/\delta)}{\varepsilon^{2}} + \log n\Big)
$$

bits of space. Combined with the matching lower bound, this settles the space complexity of distinct elements in all of $n$, $\varepsilon$ and $\delta$. The same work also treats *strong tracking*, where the estimate must be a $(1 \pm \varepsilon)$-approximation of the number of distinct elements seen so far simultaneously at every time of the stream.

## Proof sketch

Instead of taking the median of $\log(1/\delta)$ independent copies, which multiplies the $\log n$ term, a single subsampled bucket structure of size $\Theta(\varepsilon^{-2}\log(1/\delta))$ is used, with hash functions drawn from expander-walk based families so that the bucket occupancy obeys a Chernoff-type tail with failure $\delta$. The level choice and the high-order bits of the hashes are stored once and shared, and a careful encoding keeps the bucket contents at $O(1)$ amortized bits each.

## Depends on

- [Turnstile streams, support size and linear sketches of a frequency vector](turnstile-streams-and-support-size.md)

## Proof depends on

- [Kane-Nelson-Woodruff distinct-elements algorithm with O(1/eps^2 + log n) bits](optimal-space-distinct-elements-algorithm.md)
- [Omega(eps^-2 log(1/delta)) lower bounds for distinct elements and Johnson-Lindenstrauss with failure probability delta](distinct-elements-lower-bound-with-failure-probability.md)

## Sources

- Jarosław Błasiok, "Optimal streaming and tracking distinct elements with high probability", SODA (2018); ACM Trans. Algorithms 16 (2020), arXiv:1804.01642.
