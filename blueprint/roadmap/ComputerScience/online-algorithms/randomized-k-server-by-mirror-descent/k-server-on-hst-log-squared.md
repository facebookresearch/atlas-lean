# Randomized $O(\log^2 k)$-competitive k-server on HSTs

For every $k \ge 2$ and every HST, there is a randomized online $k$-server algorithm that is $O(\log^2 k)$-competitive, with the competitive ratio independent of the number of leaves and of the depth of the HST. This is the first $o(k)$-competitive randomized algorithm whose ratio does not depend on the size of the underlying HST.

## Proof sketch

Run continuous-time mirror descent with the shifted multiscale entropy, with shift $\delta = \frac{1}{2k}$, on a polytope of fractional server states; a request at a leaf pushes the anti-server mass at that leaf down to $\delta$, which yields a fractional $(k + \varepsilon)$-server algorithm that is then converted into a fractional $k$-server algorithm at a constant-factor loss. The Bregman potential charges offline movement at rate $O(\log(1/\delta)) = O(\log k)$, since the dual norm of $\nabla \Phi$ is $O(\log k)$. An auxiliary potential that tracks a weighted depth of the fractional server measure charges the online movement to the decrease of the Bregman potential: with combinatorial depth $D$ this gives $O(D \log k)$, and replacing depth by a fractional-server-weighted depth with time-varying weights on $\tau$-adic HSTs gives an $O(\log^2 k)$-competitive fractional algorithm. Online rounding on HSTs with separation $\tau > 5$ loses only a constant factor.

## Depends on

- [Hierarchically separated trees](../metrical-task-systems-and-hst-embeddings/hierarchically-separated-tree.md)
- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)

## Proof depends on

- [Bregman-divergence potential for mirror descent](bregman-potential-inequality.md)
- [Online rounding of fractional k-server on HSTs](../metrical-task-systems-and-hst-embeddings/fractional-to-integral-rounding-on-hst.md)
- [Multiscale entropy regularizer](multiscale-entropy.md)
- [Continuous-time mirror descent for online covering](continuous-mirror-descent-dynamics.md)
- [Fractional k-server on a tree](fractional-k-server-polytope.md)

## Sources

- Sébastien Bubeck, Michael B. Cohen, Yin Tat Lee, James R. Lee, Aleksander Mądry, "k-Server via Multiscale Entropic Regularization", STOC (2018), arXiv:1711.01085, Theorem 1.1, Lemmas 3.2–3.4, Section 3.4.
