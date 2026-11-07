# Evaluation to a value passes through every reduct

Let $t$, $t'$ and $v$ be terms of the
same type in the same context, with $v$ a value. If $t$ evaluates to $v$ and $t$ evaluates to
$t'$, each in finitely many call-by-value steps, then $t'$ evaluates to $v$ in finitely many
steps.

The value endpoint makes the first evaluation maximal, so every other finite
evaluation is one of its prefixes.
