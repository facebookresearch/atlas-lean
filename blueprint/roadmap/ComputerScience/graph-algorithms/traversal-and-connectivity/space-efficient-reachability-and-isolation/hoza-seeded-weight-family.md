# Hoza's seeded weight family

Fix a binary code assigning a codeword $\gamma(c) \in \{0,1\}^\ell$ to each column $c$ (for example a Justesen-type code over a finite field with polynomial alphabet). For a **seed** $z \in \{0,1\}^\ell$, define the weight of vertex $(i, c)$ with $i \ge 1$ by

$$
\mathrm{wt}_z(i, c) = 6^{\,e(i)} \sum_{b=1}^{\ell} 6^{\,\ell - b}\, z_b\, \gamma(c)_b ,
$$

where $e(i)$ is determined by the $2$-adic valuation of the layer index $i$ (scaled so that within any interval of layers the unique layer of maximal $2$-adic valuation dominates). The masked base-six place values give priority to earlier codeword bits, and the layer factor gives priority to the dominant internal layer of every path interval.

## Depends on

- [Layered digraphs and min-isolating weights](layered-digraphs-and-min-isolation.md)

## Sources

- W. M. Hoza, "NL = UL", Electronic Colloquium on Computational Complexity, Report TR26-323, 2026.
- J. Justesen, "A Class of Constructive Asymptotically Good Algebraic Codes", IEEE Transactions on Information Theory 18(5), 1972.
