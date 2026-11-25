# State and clocks after $n$ steps of a two-channel chain

For a [two-channel chain](two-channel.md), a natural number `n` and a pair `(x, c)` of a state and
a [clock configuration](clock-config.md), the state and clocks after `n` jumps are the `n`-th
iterate of the [step map](step.md) applied to `(x, c)`; for `n = 0` this is `(x, c)` itself. The
step map leaves a state `y` with `rate₁ y + rate₂ y = 0` and its clocks unchanged, so once the
chain reaches such a state the later steps are trivial, and they are counted among the `n`.
