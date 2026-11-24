# Commands of IMP

The commands of the while-language IMP are built inductively from skip
and the assignments $x_i := a$ of an arithmetic expression $a$ to the variable $x_i$ with index
$i \in \mathbb{N}$: if $c$, $c_1$ and $c_2$ are commands and $b$ is a Boolean expression, then so
are the sequential composition $c_1 ; c_2$, the conditional if $b$ then $c_1$ else $c_2$, and the
loop while $b$ do $c$.
