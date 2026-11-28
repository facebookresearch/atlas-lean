# Lattice scores have no one-sequence tail with K ≠ 0

Let `q` and `f` be real weights and scores on a finite alphabet, `θ > 0`, `h > 0` and `K ≠ 0`, with
every score `f b` in the lattice `hℤ`. Then `(q, f)` does not have the
[one-sequence tail](../../../Biology/bioinformatics/sequence-alignment/two-sequence-karlin-altschul-statistics/one-sequence-tail.md) with constants `θ` and `K`, the asymptotic
`P(M_L > t) = (K + o(1)) L e^{-θ t}`, uniformly as `L → ∞` and `L e^{-θ t} → 0` over thresholds
`t ≤ η L`, of the [score probability](score-prob.md)
of `{M_L > t}`: by [the lattice case](eq-zero-of-lattice.md) it would force `K = 0`.
