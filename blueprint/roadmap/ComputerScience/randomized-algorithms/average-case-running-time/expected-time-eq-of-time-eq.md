# Constant running time on the support gives that expected time

Let $A$ be an algorithm
on inputs of a type $\gamma$ whose running time $T_A(x)$ on each input $x$ is a natural number,
let $D$ be a probability mass function on $\gamma$, and let $c$ be a natural number. If
$T_A(x) = c$ for every input $x$ in the support of $D$, then the expected running time of $A$
under $D$ equals $c$.

Inputs outside the support have probability $0$, so their running times do not contribute.
