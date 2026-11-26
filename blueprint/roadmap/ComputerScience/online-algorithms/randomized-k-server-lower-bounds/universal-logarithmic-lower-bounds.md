# Universal logarithmic lower bounds for randomized k-server and MTS

For all integers $k < n$ and every $n$-point metric space, the randomized competitive ratio of the $k$-server problem is $\Omega(\log k)$, and the randomized competitive ratio of metrical task systems is $\Omega(\log n)$. Both bounds are asymptotically tight for suitable families of metrics, and they improve the previous universal bounds $\Omega(\log k / \log\log k)$ and $\Omega(\log n / \log\log n)$.

## Proof sketch

Bubeck, Coester and Rabani design, for an arbitrary metric, a randomized adversary that exploits the scale structure of the metric: at every scale where the metric has enough points, the adversary forces any online algorithm to pay a constant fraction of the offline cost at that scale beyond what the optimum pays, and a potential argument shows that these contributions add up over $\Omega(\log k)$ (respectively $\Omega(\log n)$) scales; Yao's principle then gives the bound against randomized algorithms.

## Depends on

- [Some $(k+1)$-point metrics force $\Omega(\log^2 k)$ randomized k-server ratio](k-server-log-squared-lower-bound.md)

## Proof depends on

- [Some $(k+1)$-point metrics force $\Omega(\log^2 k)$ randomized k-server ratio](k-server-log-squared-lower-bound.md)

## Sources

- Sébastien Bubeck, Christian Coester, Yuval Rabani, "The Randomized k-Server Conjecture Is False!", STOC (2023), arXiv:2211.05753.
