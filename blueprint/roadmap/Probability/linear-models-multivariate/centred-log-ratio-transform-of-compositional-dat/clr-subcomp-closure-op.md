# Closing before taking a subcomposition leaves its CLR unchanged

Let $\iota$ be a finite set with at least one part, $S \subseteq \iota$ a set of parts and $x$
a [positive composition](pos-composition.md) on $\iota$ (so $x_i > 0$ for every $i$). Then
taking the [subcomposition](subcomp.md) on $S$ of the [closure](closure-op.md)
$\mathcal{C}(x) = \bigl(x_i / \sum_{j \in \iota} x_j\bigr)_{i \in \iota}$ instead of $x$ does
not change its [CLR transform](clr.md) over the parts of $S$:
$\operatorname{clr}\bigl(\mathcal{C}(x)_S\bigr) = \operatorname{clr}(x_S)$.
