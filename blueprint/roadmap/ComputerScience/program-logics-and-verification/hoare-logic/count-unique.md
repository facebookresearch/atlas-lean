# Uniqueness of the loop iteration count

Let $b$ be a boolean expression, $c$ a command
and $s$ a state. If the loop $\mathtt{while}\ b\ \mathtt{do}\ c$, started in $s$, exits in
a state $t$ after exactly $n$ executions of the body and also exits in a state $t'$ after
exactly $m$ executions of the body, then $n = m$.
