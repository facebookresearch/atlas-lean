# Trained weights classify every example

Let $K$ be a commutative ring with a linear order,
$\iota$ a finite type, and $v \cdot w = \sum_{i \in \iota} v_i w_i$ the dot product on $K^\iota$.
Let $L$ be a finite list of labelled examples $(x, y)$ with $x \in K^\iota$ and $y$ a Boolean. For
every natural number $n$ and all weights $w, v \in K^\iota$, if training on $L$ from $w$ with at
most $n$ passes returns $v$, then every example $(x, y)$ in $L$ satisfies
$0 < \operatorname{sign}(y)\,(v \cdot x)$.
