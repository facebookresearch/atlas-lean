# Exact expected probe complexity of uniform probing

Under uniform probing in an array of $n$ slots, the key inserted when exactly $k$ slots are occupied ($0 \le k < n$) has expected probe complexity $\frac{n+1}{n-k+1}$. Consequently, after $m = n - \lfloor \delta n \rfloor$ insertions the amortized expected probe complexity equals $\frac{n+1}{m}\left(H_{n+1} - H_{n-m+1}\right)$, where $H_j$ is the $j$-th harmonic number, which is $\Theta(\log \delta^{-1})$ for $\delta \le 1/2$, and the worst-case expected probe complexity is $\frac{n+1}{\lfloor \delta n \rfloor + 2} = (1 + o(1))\,\delta^{-1}$ for fixed $\delta$.

## Proof sketch

The first $j-1$ entries of a uniformly random permutation hit occupied slots with probability $\binom{k}{j-1}/\binom{n}{j-1}$, and summing these tail probabilities over $j \ge 1$ gives the hockey-stick identity $\sum_{j \ge 0} \binom{k}{j}/\binom{n}{j} = \frac{n+1}{n-k+1}$. Averaging $\frac{n+1}{n-k+1}$ over $k = 0, \dots, m-1$ telescopes into the harmonic difference, and $H_{n+1} - H_{\lfloor\delta n\rfloor + 1} = \ln \delta^{-1} + O(1)$. The last insertion occurs at $k = m-1$.

## Depends on

- [Greedy open addressing and uniform probing](greedy-open-addressing-and-uniform-probing.md)
- [Amortized, worst-case and high-probability probe complexity](amortized-and-worst-case-probe-complexity.md)
- [Expected probes in open addressing](../hashing-analysis/expected-probes-in-open-addressing.md)

## Proof depends on

- [Greedy open addressing and uniform probing](greedy-open-addressing-and-uniform-probing.md)
- [Amortized, worst-case and high-probability probe complexity](amortized-and-worst-case-probe-complexity.md)
- [Expected probes in open addressing](../hashing-analysis/expected-probes-in-open-addressing.md)

## Sources

- Donald E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd ed., Addison-Wesley (1998).
- Andrew C. Yao, "Uniform Hashing Is Optimal", Journal of the ACM 32(3) (1985).
