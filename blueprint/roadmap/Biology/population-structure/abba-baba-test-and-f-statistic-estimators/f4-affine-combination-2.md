# qpAdm model equation in the drift model

Let $M$ be a [drift model](../patterson-s-f-statistics/drift-model.md) on a measure $\mu$ with lineage weights $w(X, e)$ and population frequencies $p_X$. Let $T, X, Y, Z$ be populations, $\iota$ a finite set, $S : \iota \to$ populations and $c \in \mathbb{R}^\iota$ with $\sum_k c_k = 1$ (of any sign) such that $w(T, e) = \sum_k c_k\, w(S_k, e)$ for every edge $e$. Then

$$f_4(T, X; Y, Z) = \sum_{k \in \iota} c_k\, f_4(S_k, X; Y, Z),$$

where $f_4$ is the [f4-statistic](../patterson-s-f-statistics/f4.md) of the frequencies $p_X$.
