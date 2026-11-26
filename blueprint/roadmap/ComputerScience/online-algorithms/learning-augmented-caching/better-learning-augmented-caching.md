# Near-optimal learning-augmented caching

For paging with cache size $k$ and next-arrival predictions, there is a randomized online algorithm with competitive ratio $O\!\left(1 + \min\!\left\{1, \frac{\eta}{k\,\mathrm{OPT}}\right\} \log k\right)$; in particular it is $O(1)$-consistent and $O(\log k)$-robust, and its dependence on $\eta$ matches the lower bound up to the inner logarithm.

## Proof sketch

Wei runs the *blind oracle* algorithm, which evicts the page with the furthest predicted next arrival and whose excess cost is $O(\eta/k)$ over the optimum by a direct charging argument, together with the randomized marking algorithm, and combines the two with a randomized algorithm-combination scheme for metrical task systems that loses only a constant factor.

## Depends on

- [Next-arrival predictions for paging](next-arrival-predictions.md)
- [Consistency and robustness of learning-augmented online algorithms](consistency-and-robustness.md)

## Proof depends on

- [Combining online algorithms for metrical task systems](combining-online-algorithms.md)
- [The randomized marking algorithm and the harmonic lower bound for paging](../competitive-paging/randomized-marking-algorithm-and-the-harmonic-lower-bound.md)

## Sources

- Alexander Wei, "Better and Simpler Learning-Augmented Online Caching", APPROX/RANDOM (2020), arXiv:2005.13716.
- Avrim Blum, Carl Burch, "On-Line Learning and the Metrical Task System Problem", Machine Learning 39(1) (2000).
