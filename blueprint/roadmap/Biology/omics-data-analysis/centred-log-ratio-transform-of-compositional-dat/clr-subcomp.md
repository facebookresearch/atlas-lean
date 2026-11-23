# CLR of a subcomposition is the re-centred restriction of the full CLR

Let $\iota$ be a finite set of parts, $x$ a [positive composition](pos-composition.md) on
$\iota$ (so $x_i > 0$ for every $i$), $S \subseteq \iota$ a set of parts and $i \in S$, so that
$S$ is nonempty. Then the [CLR transform](clr.md) of the [subcomposition](subcomp.md)
$x_S = (x_k)_{k \in S}$, taken over the $|S|$ parts of $S$, is

$$
\operatorname{clr}(x_S)_i
= \operatorname{clr}(x)_i - \frac{1}{|S|} \sum_{j \in S} \operatorname{clr}(x)_j .
$$

So the CLR of a subcomposition is the restriction of the full CLR to $S$, re-centred to have
mean zero over $S$.
