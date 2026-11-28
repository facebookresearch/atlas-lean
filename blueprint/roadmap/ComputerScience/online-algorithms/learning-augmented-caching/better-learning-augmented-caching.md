# Near-optimal learning-augmented caching

For paging with cache size $k \ge 2$ and next-arrival predictions with $\ell_1$ error $\eta$, the *BlindOracle* algorithm, which on a miss evicts the cached page whose predicted next arrival is latest, has competitive ratio at most

$$
\min\left\{1 + 2\,\frac{\eta}{\mathrm{OPT}},\; 2 + \frac{4}{k-1}\cdot\frac{\eta}{\mathrm{OPT}}\right\}.
$$

Combining it with an $H_k$-competitive randomized paging algorithm gives, for every $\varepsilon \in (0, 1/4)$, a randomized algorithm with competitive ratio

$$
(1 + \varepsilon)\min\left\{1 + 2\,\frac{\eta}{\mathrm{OPT}},\; 2 + \frac{4}{k-1}\cdot\frac{\eta}{\mathrm{OPT}},\; H_k\right\} = O\!\left(1 + \min\left\{\frac{\eta}{k\,\mathrm{OPT}},\; \log k\right\}\right),
$$

so it is $(1+\varepsilon)$-consistent and $O(\log k)$-robust. Combining BlindOracle with a deterministic $k$-competitive algorithm such as LRU gives a deterministic algorithm with ratio $2\min\{1 + 2\eta/\mathrm{OPT},\, 2 + \frac{4}{k-1}\eta/\mathrm{OPT},\, k\}$, and every deterministic algorithm has ratio $1 + \Omega(\min\{\eta/(k\,\mathrm{OPT}),\, k\})$, so the deterministic combination is optimal up to constant factors.

## Proof sketch

Wei relates the $\ell_1$ error to the number of inversions of the predicted next-arrival order (Rohatgi's lemma: $\eta$ is at least half the number of inversions) and charges each extra eviction of BlindOracle to inversions, which gives the two bounds on BlindOracle. The combined algorithms come from black-box combiners: the deterministic follow-the-better-algorithm scheme of Fiat, Karp, Luby, McGeoch, Sleator and Young (ratio $2$ times the better of two algorithms, plus a constant), and the multiplicative-weights scheme of Blum and Burch (ratio $1 + \varepsilon$ plus an additive $O(k/\varepsilon)$), applied with the Equitable algorithm of Achlioptas, Chrobak and Noga, which is $H_k$-competitive. The deterministic lower bound builds request sequences on which every deterministic algorithm pays $\mathrm{OPT} + \Omega(\eta/k)$.

## Depends on

- [Next-arrival predictions for paging](next-arrival-predictions.md)
- [Consistency and robustness of learning-augmented online algorithms](consistency-and-robustness.md)

## Proof depends on

- [Combining online algorithms for metrical task systems](combining-online-algorithms.md)
- [The randomized marking algorithm and the harmonic lower bound for paging](../competitive-paging/randomized-marking-algorithm-and-the-harmonic-lower-bound.md)

## Sources

- Alexander Wei, "Better and Simpler Learning-Augmented Online Caching", APPROX/RANDOM (2020), arXiv:2005.13716, Theorem 1.1, Corollaries 1.2 and 1.3, Theorem 1.4.
- Avrim Blum, Carl Burch, "On-Line Learning and the Metrical Task System Problem", Machine Learning 39(1) (2000).
- Dimitris Achlioptas, Marek Chrobak, John Noga, "Competitive Analysis of Randomized Paging Algorithms", Theoretical Computer Science 234 (2000).
