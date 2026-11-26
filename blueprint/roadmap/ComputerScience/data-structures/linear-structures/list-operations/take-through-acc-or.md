# Disjunction accumulator gives the inclusive first-hit prefix

Let $p$ be a test that is true or false on each element and $L$ a list. Take true/false values as
accumulators, the update $f(b, x) = b \lor p(x)$, the stopping test that is true exactly on the
value true, and the initial accumulator false. The resulting accumulator-stopped prefix of $L$
equals the inclusive first-hit prefix of $L$ for $p$.
