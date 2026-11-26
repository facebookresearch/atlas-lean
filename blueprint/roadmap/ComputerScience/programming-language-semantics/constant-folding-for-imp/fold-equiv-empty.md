# Constant folding from the empty table preserves all terminating IMP executions

Let $\operatorname{fold}_\emptyset(c)$ be the constant folding and propagation of the IMP command $c$ starting from the empty constant table, which records no known value. For every command $c$ and all states $s, f$, $\operatorname{fold}_\emptyset(c)$ run from $s$ terminates in $f$ under the big-step semantics if and only if $c$ run from $s$ terminates in $f$.
