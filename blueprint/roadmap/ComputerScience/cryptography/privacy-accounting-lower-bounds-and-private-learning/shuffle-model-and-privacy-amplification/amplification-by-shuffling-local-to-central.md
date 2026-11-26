# Amplification by shuffling from local to central privacy

Let $R$ be an $\varepsilon_0$-differentially private local randomizer with $\varepsilon_0$ bounded by a constant. Applying $R$ to each of $n$ records and shuffling the reports (equivalently, any permutation-invariant protocol built from $\varepsilon_0$-local randomizers) is $(\varepsilon, \delta)$-differentially private in the central sense with

$$
\varepsilon = O\!\left(\varepsilon_0 \sqrt{\frac{\log(1/\delta)}{n}}\right),
$$

for $n$ large enough relative to $\log(1/\delta)$. Thus the noise and $\sqrt{n}$ accuracy overhead of local protocols correspond to much stronger central privacy once the reports are anonymized, and repeated collection of changing values can be done with privacy cost polylogarithmic in the number of changes.

## Proof sketch

Consider the reports in the order in which a random permutation assigns them; the differing record's report is hidden among $n$ reports, each of which, by local privacy, could have come from the differing record with probability ratio at most $e^{\varepsilon_0}$. Bounding the privacy loss of this mixture via a martingale argument over the random positions, or directly by the clone reduction, gives a loss concentrated at scale $\varepsilon_0\sqrt{\log(1/\delta)/n}$.

## Depends on

- [Local randomizers and the shuffle model](shuffle-model.md)

## Proof depends on

- [Hiding among the clones: nearly optimal amplification by shuffling](amplification-by-shuffling-clones-bound.md)

## Sources

- U. Erlingsson, V. Feldman, I. Mironov, A. Raghunathan, K. Talwar, A. Thakurta, "Amplification by Shuffling: From Local to Central Differential Privacy via Anonymity", SODA (2019), arXiv:1811.12469.
- V. Feldman, A. McMillan, K. Talwar, "Hiding Among the Clones: A Simple and Nearly Optimal Analysis of Privacy Amplification by Shuffling", FOCS (2021), arXiv:2012.12803.
