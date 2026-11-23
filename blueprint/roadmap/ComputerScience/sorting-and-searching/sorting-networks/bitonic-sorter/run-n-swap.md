# Reversing the comparators conjugates the network by complement on Booleans

Let $ps$ be
a list of comparators on $\mathbb{N}$-indexed wires and let $ps'$ be obtained by replacing each
comparator $(i, j)$ in $ps$ by $(j, i)$. For every input $f : \mathbb{N} \to \mathrm{Bool}$ and
every wire $x$, the value of wire $x$ after running $ps'$ on $f$ is the negation of the value of
wire $x$ after running $ps$ on the complemented input $y \mapsto \lnot f(y)$.
