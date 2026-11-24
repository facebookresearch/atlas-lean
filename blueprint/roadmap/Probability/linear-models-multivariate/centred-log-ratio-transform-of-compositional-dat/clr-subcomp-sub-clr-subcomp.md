# CLR differences in a subcomposition equal those of the whole

Let $\iota$ be a finite set of parts, $x$ a [positive composition](pos-composition.md) on
$\iota$ (so $x_i > 0$ for every $i$), $S \subseteq \iota$ a set of parts and $i, j \in S$. Then
a difference of two [CLR](clr.md) coordinates is the same whether it is computed from the
[subcomposition](subcomp.md) $x_S = (x_k)_{k \in S}$, with the CLR over the $|S|$ parts of
$S$, or from the full composition:

$$
\operatorname{clr}(x_S)_i - \operatorname{clr}(x_S)_j
= \operatorname{clr}(x)_i - \operatorname{clr}(x)_j .
$$

Both sides equal $\log(x_i / x_j)$. This is the subcompositional coherence of log-ratio
analyses in Aitchison's sense.
