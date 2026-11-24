# Ladder renewal data for lattice scores

For a measure `P` on `Ω`, a real random variable `Y` and reals `θ` and `h`, lattice ladder renewal
data with span `h` consist of a [descending-ladder fixed point](ladder-fixed-point.md) `(D, M')` for
`Y` with `D` almost surely in `-hℕ = {0, -h, -2h, …}`, a sequence `g 0, g 1, …` of nonnegative reals
with `g 0 = 0` (the defective probabilities that the first strict ascending ladder height is `j h`),
and a real `μ_θ`, such that: `∑_j g j e^{θ h j} = 1` (the ladder Cramér identity); the greatest
common divisor of `{j : g j > 0}` is `1` (aperiodicity); `∑_j j g j e^{θ h j} = μ_θ` (a finite
tilted ladder mean); and the defective renewal equation
`P(M' > k h) = ∑_{j > k} g j + ∑_{j ≤ k} g j P(M' > (k - j) h)` holds for every natural `k`. These
are the facts that the strong Markov property provides, taken as hypotheses; no renewal theorem is
among them, and the [lattice excursion tail](tendsto-tail-2.md) follows from them.
