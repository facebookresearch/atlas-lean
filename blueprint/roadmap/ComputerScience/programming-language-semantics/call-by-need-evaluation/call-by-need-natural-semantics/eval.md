# Eval

`Eval A Γ e Δ w n`: in the heap `Γ`, choosing new names outside the set `A`, the expression
`e` evaluates to the value `w`, leaving the heap `Δ`, and performs `n` additions.

This is Launchbury's natural semantics for lazy evaluation in Sestoft's revised form, where new
heap names are chosen in the `let` rule outside the set `A` of names under evaluation, extended
here so that the first operand of an addition also avoids the names of the second operand.
