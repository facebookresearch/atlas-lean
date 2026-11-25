# Multinomial formula for the law conditioned on a state's total count

Let `S` be a finite set and `c ∈ ℝ^S` with `c_s > 0` for every `s`. For every state `x ∈ ℕ^S`, with
`n = ∑_s x_s`, the [law conditioned](conditioned-law.md) on the [set](total-class.md) of states with
total count `n` takes at `x` the multinomial value
`π_c(x | ∑ = n) = n! / ∏_s x_s! · ∏_s (c_s / ∑_{s'} c_{s'})^{x_s}`. For a fixed total `n`, the
conditioned law equals the multinomial mass function at every state of `ℕ^S`, also off that set
([as functions](conditioned-law-total-class-eq-multinomi.md)).

If every reaction of a network conserves the total count, for example conversions `A_i ⇌ A_j`
between single species, these sets are [reaction-closed](is-reaction-closed-total-class.md). For
such a network and a positive `c`
[complex balanced](../../../Biology/systems-biology/complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md)
for its rate constants, the law conditioned on each of these sets, which is this multinomial law,
therefore [solves](is-stationary-master-solution-conditione.md) the
[stationary master equation](../ergodic-theorem-for-complex-balanced-reaction-ne/is-stationary-master-solution.md)
at every state; it is a stationary law on that set, not necessarily the only one.
