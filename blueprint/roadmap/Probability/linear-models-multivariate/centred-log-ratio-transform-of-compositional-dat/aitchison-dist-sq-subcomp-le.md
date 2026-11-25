# Subcompositional dominance of the squared Aitchison distance

Let $\iota$ be a finite set of parts, $S \subseteq \iota$ a set of parts and $x, y$
[positive compositions](pos-composition.md) on $\iota$. Then the
[squared Aitchison distance](aitchison-dist-sq.md) between the [subcompositions](subcomp.md)
$x_S$ and $y_S$, computed with the [CLR transform](clr.md) over the parts of $S$, is at most
the squared Aitchison distance between $x$ and $y$:

$$
\sum_{i \in S} \bigl(\operatorname{clr}(x_S)_i - \operatorname{clr}(y_S)_i\bigr)^2
\le \sum_{i \in \iota} \bigl(\operatorname{clr}(x)_i - \operatorname{clr}(y)_i\bigr)^2 .
$$

Taking square roots, passing to a subcomposition never increases the Aitchison distance.
