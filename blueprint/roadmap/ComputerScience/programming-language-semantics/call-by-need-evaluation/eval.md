# Eval

`Eval A Γ e Δ w n`: in the heap `Γ`, choosing new names outside the set `A`, the expression
`e` evaluates to the value `w`, leaving the heap `Δ`, and performs `n` additions.

This is Launchbury's natural semantics for lazy evaluation in Sestoft's revised form, where new
heap names are chosen in the `let` rule outside the set `A` of names under evaluation, extended
here so that the first operand of an addition also avoids the names of the second operand.

The judgement places no condition on its configuration. The source semantics starts from a
closed expression in the empty heap with `A` empty, and every configuration it then reaches is
good in Sestoft's sense [Ses97, §2.5, Definition 1, Lemma 1]: among other conditions, no bound
name of the heap or of the expression is in `A` or bound in the heap. Sestoft shows that such an
evaluation involves no capture [Ses97, §2.5, Proposition 1]; this is not proved here. From a
configuration that is not good, the naive substitution of the application rule can capture: in
the heap that binds `p` to `7` and `q` to `2`, with `A` empty, the configuration
`((λx. λp. x) p) q` is closed and evaluates to `2`, because the argument `p` is captured under
`λp`, while with the inner binder renamed to a fresh name it evaluates to `7`.

The source semantics also assumes an inexhaustible supply of fresh names. Over a finite type of
names the `let` rule can run out of them, and the `let` then has no evaluation, as an allocation
failure: over `Unit`, where `x` is the only name, `let x = 7 in x` has none.
