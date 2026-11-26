# Randomized MTS has ratio $\Theta(\log^2 n)$ on some metrics

There exist $n$-point metric spaces, for infinitely many $n$, on which every randomized online algorithm for metrical task systems has competitive ratio $\Omega(\log^2 n)$. Together with the universal $O(\log^2 n)$ upper bound, this settles the worst-case randomized competitive ratio of metrical task systems as $\Theta(\log^2 n)$, the first improvement of an existential MTS lower bound since 1987.

## Proof sketch

Apply the $(k+1)$-point $k$-server lower bound with $n = k + 1$ and use the equivalence of $k$-server on $k+1$ points with the MTS on the hole; the request cost functions are valid MTS tasks.

## Depends on

- [Some $(k+1)$-point metrics force $\Omega(\log^2 k)$ randomized k-server ratio](k-server-log-squared-lower-bound.md)
- [k-server on $k+1$ points is a metrical task system](k-server-on-k-plus-one-points.md)
- [Randomized MTS is $O(\log^2 n)$-competitive on every metric](../metrical-task-systems-and-hst-embeddings/mts-log-squared-upper-bound.md)

## Proof depends on

- [Some $(k+1)$-point metrics force $\Omega(\log^2 k)$ randomized k-server ratio](k-server-log-squared-lower-bound.md)
- [k-server on $k+1$ points is a metrical task system](k-server-on-k-plus-one-points.md)
- [Randomized MTS is $O(\log^2 n)$-competitive on every metric](../metrical-task-systems-and-hst-embeddings/mts-log-squared-upper-bound.md)

## Sources

- Sébastien Bubeck, Christian Coester, Yuval Rabani, "The Randomized k-Server Conjecture Is False!", STOC (2023), arXiv:2211.05753.
- Sébastien Bubeck, Michael B. Cohen, James R. Lee, Yin Tat Lee, "Metrical Task Systems on Trees via Mirror Descent and Unfair Gluing", SIAM Journal on Computing 50(3) (2021); SODA (2019), arXiv:1807.04404.
