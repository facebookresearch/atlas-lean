# McLeish's martingale central limit theorem

**McLeish's martingale central limit theorem** (McLeish 1974, Theorem 2.3).

Let `X n k` be a martingale difference array: for each row `n` the partial sums
`∑_{j<k} X n j` form a martingale with respect to a filtration `F n`. Consider row sums over
`k < r n`. Assume
* (a) the maximal squared increment is bounded in `L¹`: `E[max_{k<r n} X n k²] ≤ B < ∞`
  eventually (stated with lower Lebesgue integrals, so the hypothesis is never vacuous);
* (b) the maximal increment tends to `0` in probability;
* (c) the realized quadratic variation `∑_{k<r n} X n k²` tends to `v` in probability.

Then the row sums converge in distribution to `N(0, v)`. No independence and no conditional
variance assumption is made: the quadratic-variation hypothesis is on the realized squares.

## Sources

- D. L. McLeish, *Dependent central limit theorems and invariance principles*, Ann. Probab. 2 (1974) 620–628, Theorem (2.3), with the proof of Theorem (2.1). McLeish normalizes `v = 1`; here `v ≥ 0` is arbitrary (`v = 0` gives convergence to `0`).
