# Furstenberg multiple recurrence theorem

Let $\mu$ be a probability measure on a measurable
space $\alpha$, let $T : \alpha \to \alpha$ be a measurable map preserving $\mu$, and let $A$ be a
measurable set with $\mu(A) > 0$. For $m \in \mathbb{N}$ write $T^{-m}(A)$ for the preimage of $A$
under the $m$-th iterate of $T$. Then for every integer $k > 0$ there is an integer $n > 0$ such
that

$$\mu\Big(\bigcap_{i=0}^{k-1} T^{-i n}(A)\Big) > 0.$$

Proof: We apply the finitary Szemerédi theorem to dense sets of return times in finite orbit
segments, using an averaging argument to obtain a positive-measure family of such segments.

## Sources

- H. Furstenberg, J. Analyse Math. 31 (1977) and Recurrence in Ergodic Theory (1981); Lean states one-transformation arithmetic-progression k-term intersection form without ergodicity hypothesis.
