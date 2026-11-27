# Loop runs with a given number of iterations

Let $b$ be a Boolean expression and $c$ a
command. For a natural number $n$ and states $s$, $s'$, the loop $\mathtt{while}\ b\ \mathtt{do}\ c$
runs from $s$ to $s'$ in $n$ iterations when, started in $s$, it exits in $s'$ after exactly $n$
executions of the body $c$. This is the least relation such that the loop runs from $s$ to $s$ in
$0$ iterations whenever $b$ evaluates to false in $s$, and the loop runs from $s$ to $s'$ in
$n + 1$ iterations whenever $b$ evaluates to true in $s$, the body $c$ has a terminating big-step
execution from $s$ to some state $t$, and the loop runs from $t$ to $s'$ in $n$ iterations.
