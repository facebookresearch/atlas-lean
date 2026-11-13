# One-step unfolding functional of a while loop

Given a Boolean expression $b$ (the guard)
and a binary relation $B$ on states (the body relation), the functional sends a relation $R$ on
states to the relation that relates $s$ to $s'$ exactly when either $b$ evaluates to false in
$s$ and $s' = s$, or $b$ evaluates to true in $s$ and there is a state $m$ with $B$ relating
$s$ to $m$ and $R$ relating $m$ to $s'$.
