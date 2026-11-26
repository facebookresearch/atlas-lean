# The randomized k-server conjecture is false

The randomized $k$-server conjecture fails: there are metric spaces with $k+1$ points on which no randomized online $k$-server algorithm is $O(\log k)$-competitive. The $\Omega(\log^2 k)$ ratio forced on these metrics matches, up to a constant factor, the $O(\log^2 k)$ ratio achievable on every HST, and also the $O(\log^2 k)$ ratio achievable on every metric with $k + 1$ points (there $k$-server is a metrical task system on $k + 1$ states, which is $O(\log^2 (k+1))$-competitive). Hence the worst-case randomized competitive ratio over metrics with $k + 1$ points is $\Theta(\log^2 k)$.

## Proof sketch

Immediate from the $\Omega(\log^2 k)$ lower bound on $(k+1)$-point metrics, since $\log^2 k / \log k \to \infty$.

## Depends on

- [The randomized k-server conjecture](../randomized-k-server-by-mirror-descent/randomized-k-server-conjecture.md)
- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)
- [Hierarchically separated trees](../metrical-task-systems-and-hst-embeddings/hierarchically-separated-tree.md)

## Proof depends on

- [Some $(k+1)$-point metrics force $\Omega(\log^2 k)$ randomized k-server ratio](k-server-log-squared-lower-bound.md)
- [Randomized $O(\log^2 k)$-competitive k-server on HSTs](../randomized-k-server-by-mirror-descent/k-server-on-hst-log-squared.md)
- [k-server on $k+1$ points is a metrical task system](k-server-on-k-plus-one-points.md)
- [Randomized MTS is $O(\log^2 n)$-competitive on every metric](../metrical-task-systems-and-hst-embeddings/mts-log-squared-upper-bound.md)

## Sources

- Sébastien Bubeck, Christian Coester, Yuval Rabani, "The Randomized k-Server Conjecture Is False!", STOC (2023), arXiv:2211.05753.
- Sébastien Bubeck, Michael B. Cohen, Yin Tat Lee, James R. Lee, Aleksander Mądry, "k-Server via Multiscale Entropic Regularization", STOC (2018), arXiv:1711.01085.
