# Kaufman-Oppenheim: local spectral expansion controls high-order random walks

Let $X$ be a pure $d$-dimensional complex in which the $1$-skeleton of the link of every $j$-face has second largest eigenvalue at most $\gamma_j$ ($-1 \le j \le d-2$). Then for every $1 \le k \le d$ the down-up walk on $(k-1)$-faces (equivalently the up-down walk on its partner level) satisfies

$$
1 - \lambda_2(\text{down-up walk on } (k-1)\text{-faces}) \ \ge\ \frac{1}{k}\prod_{j=-1}^{k-3}\big(1 - \gamma_j\big)
$$

(Kaufman-Oppenheim with the sharpened form of Alev-Lau). For a $\gamma$-local spectral expander this is at least $\frac{(1 - \gamma)^{k-1}}{k}$, so as $\gamma \to 0$ high-order walks mix almost as fast as on the complete complex.

## Proof sketch

Write the down-up and up-down walks as compositions of the up operator $U_k$ and down operator $D_{k+1}$ and use the local-to-global identity $D_{k+1}U_k - \frac{1}{k+1}I = \frac{k}{k+1}(\text{non-lazy part})$, whose non-lazy part restricted to links is a walk on link $1$-skeletons. Local spectral bounds then give an operator inequality between consecutive levels, which telescopes into the stated gap.

## Depends on

- [Up-down and down-up random walks on simplicial complexes](up-down-random-walks-on-simplicial-complexes.md)
- [Links and local spectral expanders](links-and-local-spectral-expansion.md)

## Proof depends on

- [Oppenheim's trickling-down theorem for spectral gaps](../../../Combinatorics/polytopes-simplicial-complexes/local-spectral-high-dimensional-expanders/oppenheim-trickle-down.md)

## Sources

- Tali Kaufman, Izhar Oppenheim, "High order random walks: beyond spectral gap", Combinatorica 40 (2020), APPROX-RANDOM (2018); arXiv:1707.02799.
- Vedat Levi Alev, Lap Chi Lau, "Improved analysis of higher order random walks and applications", STOC (2020); arXiv:2001.02827.
- Irit Dinur, Tali Kaufman, "High dimensional expanders imply agreement expanders", FOCS (2017).
