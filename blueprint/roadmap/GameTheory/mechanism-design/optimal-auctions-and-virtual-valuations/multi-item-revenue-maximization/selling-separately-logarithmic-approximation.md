# Selling separately loses at most a logarithmic factor for independent items

For a single additive buyer with independent item values on $n$ items, $\mathrm{SREV}(D) \ge \mathrm{REV}(D) / O(\log n)$, and this is tight: there are product distributions with $\mathrm{REV}(D) / \mathrm{SREV}(D) = \Omega(\log n)$. In general neither $\mathrm{SREV}$ nor $\mathrm{BREV}$ alone is a constant-factor approximation of $\mathrm{REV}$.

## Proof sketch

Apply the core-tail decomposition with the threshold of item $j$ at $c n\, r_j$, where $r_j$ is the item's optimal revenue. Then each item is in the tail with probability at most $1/(cn)$ and the tail contributes $O(\mathrm{SREV})$. In the core, $\Pr[v_j > x] \le r_j / x$ gives $\mathbb{E}[v_j \mid v_j \le c n r_j] = O(r_j (1 + \ln(cn)))$, so the core welfare is $O(\log n)\, \mathrm{SREV}$; with $c$ constant this gives $\mathrm{REV} \le (\ln n + O(1))\, \mathrm{SREV}$. For $n$ independent equal-revenue items $\mathrm{SREV} = n$ while bundling earns $\Theta(n \log n)$, which gives the $\Omega(\log n)$ separation; other product distributions make $\mathrm{BREV}$ alone a poor approximation.

## Depends on

- [Single additive buyer with independent item values: SREV, BREV and REV](additive-buyer-srev-brev-rev.md)

## Proof depends on

- [Core-tail decomposition of the optimal revenue](core-tail-decomposition-revenue.md)

## Sources

- X. Li, A. C.-C. Yao, "On revenue maximization for selling multiple independently distributed items", Proceedings of the National Academy of Sciences 110(28) (2013).
- S. Hart, N. Nisan, "Approximate revenue maximization with multiple items", Journal of Economic Theory 172 (2017); EC 2012.
- M. Babaioff, N. Immorlica, B. Lucier, S. M. Weinberg, "A Simple and Approximately Optimal Mechanism for an Additive Buyer", FOCS 2014; Journal of the ACM 67(4) (2020), arXiv:1405.6146, Theorem 1.
