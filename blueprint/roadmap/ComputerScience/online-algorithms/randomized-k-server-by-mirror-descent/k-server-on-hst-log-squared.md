# Randomized $O(\log^2 k)$-competitive k-server on HSTs

For every HST and every $k$, there is a randomized online $k$-server algorithm that is $O(\log^2 k)$-competitive, with the competitive ratio independent of the number of leaves and of the depth of the HST. This is the first $o(k)$-competitive randomized algorithm whose ratio does not depend on the size of the underlying HST.

## Proof sketch

Run continuous-time mirror descent with the multiscale entropy on the fractional $k$-server polytope. The Bregman potential charges the online movement against the offline movement; the multiscale choice of shifts and scales makes the Lipschitz constant of $\nabla \Phi$ at each node $O(\log k)$ times the edge length, and an additional potential term handles the depth so that each level costs $O(\log k)$ with geometric decay across levels, giving an $O(\log^2 k)$-competitive fractional algorithm. Online rounding on HSTs loses only a constant factor.

## Depends on

- [Multiscale entropy regularizer](multiscale-entropy.md)
- [Bregman-divergence potential for mirror descent](bregman-potential-inequality.md)
- [Online rounding of fractional k-server on HSTs](../metrical-task-systems-and-hst-embeddings/fractional-to-integral-rounding-on-hst.md)

## Proof depends on

- [Multiscale entropy regularizer](multiscale-entropy.md)
- [Bregman-divergence potential for mirror descent](bregman-potential-inequality.md)
- [Online rounding of fractional k-server on HSTs](../metrical-task-systems-and-hst-embeddings/fractional-to-integral-rounding-on-hst.md)

## Sources

- Sébastien Bubeck, Michael B. Cohen, Yin Tat Lee, James R. Lee, Aleksander Mądry, "k-Server via Multiscale Entropic Regularization", STOC (2018), arXiv:1711.01085.
