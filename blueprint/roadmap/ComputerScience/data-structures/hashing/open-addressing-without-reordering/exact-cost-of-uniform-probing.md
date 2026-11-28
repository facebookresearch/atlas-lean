# Exact expected probe complexity of uniform probing

Under uniform probing in an array of $n$ slots, the key inserted when exactly $k$ slots are occupied ($0 \le k < n$) has expected probe complexity $\frac{n+1}{n-k+1}$. Consequently, after $m = n - \delta n$ insertions the amortized expected probe complexity equals $\frac{n+1}{m}\left(H_{n+1} - H_{n-m+1}\right)$, where $H_j$ is the $j$-th harmonic number, and the worst-case expected probe complexity, attained by the last insertion, is $\frac{n+1}{\delta n + 2}$. In the high-load regime $1/n \le \delta \le 1/2$ with $\delta n$ an integer, the amortized cost is $\Theta(\log \delta^{-1})$ and the worst-case cost is $\Theta(\delta^{-1})$, uniformly in $n$; the worst-case cost is $(1 + o(1))\,\delta^{-1}$ as $n \to \infty$ whenever $\delta n \to \infty$, in particular for fixed $\delta$.

## Proof sketch

The first $j-1$ entries of a uniformly random permutation hit occupied slots with probability $\binom{k}{j-1}/\binom{n}{j-1}$, and summing these tail probabilities over $j \ge 1$ gives the hockey-stick identity $\sum_{j \ge 0} \binom{k}{j}/\binom{n}{j} = \frac{n+1}{n-k+1}$. Averaging $\frac{n+1}{n-k+1}$ over $k = 0, \dots, m-1$ telescopes into the harmonic difference, and for $1 \le \delta n \le n/2$ we have $H_{n+1} - H_{\delta n + 1} = \ln \delta^{-1} + O(1)$ with $\ln \delta^{-1} \ge \ln 2$, while $1 \le \frac{n+1}{m} \le 3$. The last insertion occurs at $k = m-1$, and $\frac{1}{3\delta} \le \frac{n+1}{\delta n + 2} \le \frac{2}{\delta}$ for $\delta n \ge 1$.

## Depends on

- [Greedy open addressing and uniform probing](greedy-open-addressing-and-uniform-probing.md)
- [Amortized, worst-case and high-probability probe complexity](amortized-and-worst-case-probe-complexity.md)

## Sources

- Donald E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd ed., Addison-Wesley (1998).
- Andrew C. Yao, "Uniform Hashing Is Optimal", Journal of the ACM 32(3) (1985).
