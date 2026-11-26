# Conditional binomial law of a cell count given a pair total

Let $\iota$ be a finite set of cells, $X_0, X_1, \dots$ mutually independent measurable random elements of $\iota$ on a probability space with $P(X_k = i) = p_i$ for every $k$ and $i$, and $C_i = \#\{k < n : X_k = i\}$ the cell counts of the first $n$ draws. Write $M_n(p; x) = \frac{n!}{\prod_i x_i!}\prod_i p_i^{x_i}$ if $\sum_i x_i = n$ and $M_n(p; x) = 0$ otherwise. Let $a \ne b$ be cells and $d \in \mathbb{N}$ with $P(C_a + C_b = d) > 0$. Then for every $m$

$$P(C_a = m \mid C_a + C_b = d) = \binom dm\Big(\frac{p_a}{p_a + p_b}\Big)^m\Big(\frac{p_b}{p_a + p_b}\Big)^{d-m},$$

with $d - m$ truncated at $0$ and $x/0 = 0$.

This is the conditional law used by McNemar-type exact tests.
