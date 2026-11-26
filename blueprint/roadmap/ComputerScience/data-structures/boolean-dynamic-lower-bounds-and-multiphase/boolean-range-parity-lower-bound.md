# Larsen–Weinstein–Yu: super-logarithmic lower bound for range parity

Every dynamic cell-probe structure for two-dimensional range parity with $w = \Theta(\lg n)$ and amortized update time $t_u = (\lg n)^{O(1)}$ has query time $t_q = \tilde{\Omega}(\lg^{1.5} n)$, where $\tilde{\Omega}$ hides $(\lg\lg n)^{O(1)}$ factors. Similar bounds hold for Boolean dynamic polynomial evaluation and two-dimensional rectangle stabbing, and for range selection and range median; the bound implies the first $\omega(\lg n)$ lower bound for classical two-dimensional range counting.

## Proof sketch

Larsen, Weinstein and Yu simulate the dynamic structure *weakly*: from a small set of cells written in one epoch, a one-way communication protocol predicts the parity answer of a random query with small but non-negligible advantage over random guessing. The simulation uses low-degree Chebyshev polynomials to amplify the correlation between the answer and the sampled cells, and a peak-to-average lemma to show that a structure with too few probes into the epoch yields too good a predictor, contradicting the small discrepancy of inner-product-like functions arising from the epoch's geometry.

## Depends on

- [Dynamic two-dimensional range parity](range-parity-problem.md)
- [Amortized update and query cost of a dynamic cell-probe structure](../dynamic-information-transfer-lower-bounds/amortized-cell-probe-costs.md)

## Proof depends on

- [Cell-sampling lemma](../cell-sampling-and-range-counting-lower-bounds/cell-sampling-lemma.md)

## Sources

- Kasper Green Larsen, Omri Weinstein, Huacheng Yu, "Crossing the Logarithmic Barrier for Dynamic Boolean Data Structure Lower Bounds", STOC (2018); SIAM Journal on Computing (2020), arXiv:1703.03575.
