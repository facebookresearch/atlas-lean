# With at least one part, every positive total occurs in each CLR fibre

Let $\iota$ be a finite set with at least one part, $x$ a
[positive composition](pos-composition.md) on $\iota$ (so $x_i > 0$ for every $i$) and $T > 0$.
Then there is a positive composition $y$ on $\iota$ with the same [CLR transform](clr.md),
$\operatorname{clr}(y) = \operatorname{clr}(x)$, and with total $\sum_{i \in \iota} y_i = T$;
for example $y = t \cdot x = (t x_i)_{i \in \iota}$ with $t = T / \sum_{j \in \iota} x_j$. So
each fibre of the CLR transform, the set of positive compositions sharing one CLR transform,
contains compositions of every positive total. With no parts every composition has total $0$,
so the statement fails for an empty set of parts.
