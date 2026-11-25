# A stationary weight with integrable rates prevents explosion

**A stationary weight with integrable rates prevents explosion** (Anderson–Cappelletti–
Koyama–Kurtz 2018, Theorem 2). Let `σ` be countable with measurable singletons and let the rates
`q` satisfy Condition 1: `q x y ≥ 0`; for every `x` the off-diagonal rates `y ↦ q x y` are
summable; and for every `x`, `y ↦ q y x` is bounded above. Let `π` be a probability distribution
(`π x ≥ 0`, `∑ π = 1`) that is a constant solution of the forward equation: for every `x`, the
family `y ↦ π y q y x` (`y ≠ x`) is summable with sum `π x q(x)`; and assume `x ↦ π x q(x)` is
summable. Let `P` be the jump kernel of the rates (`P x y = q(x, y)/q(x)` for `y ≠ x`, and
`P x x = 1` at an absorbing state, `jumpProb q`), and run the jump–hold chain
`StochasticCRNNonExplosion.JumpHold` with this kernel and holding rate `holdRate q` (the total
rate `q(x)`, padded to `1` at an absorbing state by a fictitious self-loop, so that the jump
times count jump–hold clock epochs, which diverge almost surely even from an absorbing state).
Then from every initial state `x₀` in the support of `π` (`π x₀ ≠ 0`) the chain is
non-explosive: almost surely its jump times tend to infinity.

## Sources

- D. F. Anderson, D. Cappelletti, M. Koyama, T. G. Kurtz, "Non-explosivity of stochastically modeled reaction networks that are complex balanced", Bull. Math. Biol. 80 (2018) 2561–2579, Theorem 2.
