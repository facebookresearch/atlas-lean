# A subcomposition's CLR is unchanged by rescaling the composition

Let $x$ be a [positive composition](pos-composition.md) on a set of parts $\iota$ (so
$x_i > 0$ for every $i$; $\iota$ need not be finite), $S \subseteq \iota$ a finite set of parts
and $t > 0$. Then the [subcomposition](subcomp.md) on $S$ of the
[rescaled composition](smul.md) $t \cdot x = (t x_i)_{i \in \iota}$ has the same
[CLR transform](clr.md), over the parts of $S$, as the subcomposition of $x$:
$\operatorname{clr}\bigl((t \cdot x)_S\bigr) = \operatorname{clr}(x_S)$. In particular the CLR
of a subcomposition does not change when the full composition is rescaled to another total.
