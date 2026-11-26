# Lower bound for caching with next-arrival predictions

For paging with cache size $k$ and next-arrival predictions, every (randomized) online algorithm has competitive ratio $\Omega\!\left(\log \min\!\left\{\frac{\eta}{k\,\mathrm{OPT}},\; k\right\}\right)$ on suitable instances, where $\eta$ is the $\ell_1$ prediction error.

## Proof sketch

Rohatgi embeds the classical randomized paging lower bound on $k+1$ pages into instances where the predictions are correct except for a budget of errors spread to hide which page will be requested next in each phase; the algorithm can be confused on only about $\eta/(k\,\mathrm{OPT})$ pages per phase, and Yao's principle with the harmonic lower bound on those pages gives the logarithm.

## Depends on

- [Next-arrival predictions for paging](next-arrival-predictions.md)

## Proof depends on

- [Yao's minimax principle](../../../TheoryOfComputation/randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)
- [The randomized marking algorithm and the harmonic lower bound for paging](../competitive-paging/randomized-marking-algorithm-and-the-harmonic-lower-bound.md)

## Sources

- Dhruv Rohatgi, "Near-Optimal Bounds for Online Caching with Machine Learned Advice", SODA (2020), arXiv:1910.12172.
