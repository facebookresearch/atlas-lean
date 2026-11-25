# Running an oracle algorithm

Given a function $O : X \to Y$, the run of an oracle
algorithm with queries in $X$, answers in $Y$ and outputs in $\alpha$ is its output when every
query $x$ is answered by $O(x)$: an algorithm that stops with output $a$ runs to $a$, and one
that queries $x$ and continues with $k(y)$ on answer $y$ runs to the run of $k(O(x))$.
