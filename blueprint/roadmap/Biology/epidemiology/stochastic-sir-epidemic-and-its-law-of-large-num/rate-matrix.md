# Rate matrix of a two-channel chain

For a [two-channel chain](two-channel.md) on a state space `ι`, with rates `rate₁, rate₂` and
targets `target₁, target₂`, the rate matrix `Q` has the entries, for states `x` and `y`,

- `Q(x, x) = -(rate₁ x + rate₂ x)`;
- for `y ≠ x`, `Q(x, y) = [target₁ x = y] rate₁ x + [target₂ x = y] rate₂ x`, where `[·]` is `1`
  when the condition holds and `0` otherwise.

Off the diagonal, row `x` thus carries `rate₁ x` at `target₁ x` and `rate₂ x` at `target₂ x`,
added up when the two targets coincide; the target `target₁₂` of simultaneous jumps plays no role.
The diagonal entry does not depend on the targets: for a chain that is not valid, a channel whose
target is `x` itself can have a nonzero rate, which enters `Q(x, x)` with no compensating
off-diagonal entry. For a [valid](is-valid.md) chain on a finite state space, `Q` is a
[rate matrix](../../../Probability/markov-chains/finite-continuous-time-markov-chains/rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md):
its off-diagonal entries are nonnegative and each row sums to `0`.
