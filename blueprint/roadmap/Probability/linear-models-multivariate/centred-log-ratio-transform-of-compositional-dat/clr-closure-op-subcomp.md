# Closing a subcomposition leaves its CLR unchanged

Let $x$ be a [positive composition](pos-composition.md) on a set of parts $\iota$ (so
$x_i > 0$ for every $i$; $\iota$ need not be finite) and $S \subseteq \iota$ a nonempty finite
set of parts. The closed [subcomposition](subcomp.md)
$\mathcal{C}(x_S) = \bigl(x_i / \sum_{j \in S} x_j\bigr)_{i \in S}$, Aitchison's
subcomposition with total $1$, has the same [CLR transform](clr.md) as the unclosed one:
$\operatorname{clr}(\mathcal{C}(x_S)) = \operatorname{clr}(x_S)$. This is the case $x_S$ of
[closing a composition leaves its CLR unchanged](clr-closure-op.md). So, when $\iota$ is
finite, the CLR of the closed subcomposition at $i \in S$ is also
$\operatorname{clr}(x)_i - \frac{1}{|S|} \sum_{j \in S} \operatorname{clr}(x)_j$, by the
[re-centring formula](clr-subcomp.md).
