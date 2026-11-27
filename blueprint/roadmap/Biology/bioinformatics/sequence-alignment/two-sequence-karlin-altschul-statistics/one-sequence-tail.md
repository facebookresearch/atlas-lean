# One-sequence tail hypothesis for the maximal segment score

For real weights `q` and real scores `f` on a finite alphabet and real constants `θ` and `K`, the
one-sequence tail holds when for every `ε > 0` there are a natural number `L₀` and reals `δ > 0`
and `η > 0` such that `|P(M_L > t) - K L e^{-θ t}| ≤ ε L e^{-θ t}` for every `L ≥ L₀` and every
real `t` with `L e^{-θ t} ≤ δ` and `t ≤ η L`. Here `P(M_L > t)` is the
[score probability](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/score-prob.md) that the
[maximal segment score](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/max-seg-score.md) of the
scores of `L` letters exceeds `t`; when `q` is a probability vector it is a probability for `L`
independent letters of law `q`. Informally `P(M_L > t) = (K + o(1)) L e^{-θ t}` as `L → ∞` and
`L e^{-θ t} → 0`, uniformly over thresholds `t ≤ η L`, where `δ` and `η` may depend on the
accuracy `ε`. It is the uniform form of the Iglehart (1972) and Karlin–Dembo (1992) tail that the
two-sequence problem needs, and an assumption on `(q, f)`, not derived from them.

The cap `t ≤ η L` matters: the scores are bounded, so `P(M_L > t) = 0` once `t ≥ L c` with
`c = max(0, max_b f(b))`, and without the cap the bound with `θ > 0` would force `K = 0`. The
definition has no nonlattice condition and is meant for nonlattice scores with `K > 0`: when every
score lies on a lattice `hℤ` with `h > 0` and `θ > 0`, it [forces `K = 0`](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/eq-zero-of-lattice.md).
It does hold with `K = 0`, for instance for the zero score and any `θ > 0`.
