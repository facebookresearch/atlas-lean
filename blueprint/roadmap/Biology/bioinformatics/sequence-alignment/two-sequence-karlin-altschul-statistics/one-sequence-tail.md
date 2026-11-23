# One-sequence tail input

**One-sequence tail input** for the maximal segment score `M_L` of `L` iid scores with law
`(q, f)`: `P(M_L > t) = (K + o(1)) L e^{-θ t}` as `L → ∞` and `L e^{-θ t} → 0`, uniformly over
thresholds `t ≤ η L` for some `η > 0`. This is the Iglehart (1972) / Karlin–Dembo (1992) tail in
the form the two-sequence problem needs; it is a hypothesis here, not derived.

The cap `t ≤ η L` is necessary: scores are bounded, so `P(M_L > t) = 0` once `t` exceeds `L` times
the largest score, and without the cap the relative-error bound would force `K = 0`. The classical
asymptotic holds only below the slope of the walk under the tilted law, which a small `η`
respects. The definition carries no nonlattice hypothesis. It is meant for the nondegenerate
classical regime `K > 0` of nonlattice scores: for nondegenerate scores on a lattice `hℤ` the
classical ratio `P(M_L > t) / (L e^{-θ t})` oscillates with the fractional part of `t / h`
(compare `LatticeRenewalInput` in `GumbelTail`). It also holds in degenerate cases: the
lattice-valued zero score satisfies it with `K = 0` (`oneSequenceTail_s0` in the test file).
