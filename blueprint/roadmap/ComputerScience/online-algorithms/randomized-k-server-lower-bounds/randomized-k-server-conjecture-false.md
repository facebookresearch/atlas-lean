# The randomized k-server conjecture is false

The randomized $k$-server conjecture fails: there are metric spaces with $k+1$ points on which no randomized online $k$-server algorithm is $O(\log k)$-competitive. Combined with the $O(\log^2 k)$ upper bound on HSTs, the optimal randomized ratio over all HSTs (and over all metrics with $k + 1$ points) is $\Theta(\log^2 k)$ up to the gap between the two constructions.

## Proof sketch

Immediate from the $\Omega(\log^2 k)$ lower bound on $(k+1)$-point metrics, since $\log^2 k / \log k \to \infty$.

## Depends on

- [Some $(k+1)$-point metrics force $\Omega(\log^2 k)$ randomized k-server ratio](k-server-log-squared-lower-bound.md)
- [Randomized $O(\log^2 k)$-competitive k-server on HSTs](../randomized-k-server-by-mirror-descent/k-server-on-hst-log-squared.md)

## Proof depends on

- [Some $(k+1)$-point metrics force $\Omega(\log^2 k)$ randomized k-server ratio](k-server-log-squared-lower-bound.md)
- [Randomized $O(\log^2 k)$-competitive k-server on HSTs](../randomized-k-server-by-mirror-descent/k-server-on-hst-log-squared.md)

## Sources

- Sébastien Bubeck, Christian Coester, Yuval Rabani, "The Randomized k-Server Conjecture Is False!", STOC (2023), arXiv:2211.05753.
- Sébastien Bubeck, Michael B. Cohen, Yin Tat Lee, James R. Lee, Aleksander Mądry, "k-Server via Multiscale Entropic Regularization", STOC (2018), arXiv:1711.01085.
