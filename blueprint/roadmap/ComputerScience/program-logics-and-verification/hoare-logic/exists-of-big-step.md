# Every terminating loop run has an iteration count

Let $b$ be a Boolean expression, $c$ a
command and $s$, $s'$ states. If the loop $\mathtt{while}\ b\ \mathtt{do}\ c$ has a terminating
big-step execution from $s$ to $s'$, then there is a natural number $n$ such that the loop,
started in $s$, exits in $s'$ after exactly $n$ executions of the body $c$.
