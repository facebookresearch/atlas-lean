# Counted loop runs are big-step executions

Let $b$ be a boolean expression, $c$ a
command, $n$ a natural number and $s$, $t$ states. If the loop
$\mathtt{while}\ b\ \mathtt{do}\ c$, started in $s$, exits in $t$ after exactly $n$
executions of the body $c$, then the loop $\mathtt{while}\ b\ \mathtt{do}\ c$ runs from $s$
to $t$ in the big-step semantics.
