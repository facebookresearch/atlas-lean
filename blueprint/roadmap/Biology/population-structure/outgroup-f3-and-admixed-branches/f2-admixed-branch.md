# Admixed-branch identity for f2 statistics

Let $M$ be a [drift model](../patterson-s-f-statistics/drift-model.md) with lineage weights $w$ and drift lengths $\ell$, let $a, b, c$ be distinct edges and $\alpha \in \mathbb{R}$, and let $M_x, A, B, X$ be populations with

$$w(M_x, \cdot) = \alpha\bigl(w(A, \cdot) + \mathbf{1}_a\bigr) + (1 - \alpha)\bigl(w(B, \cdot) + \mathbf{1}_b\bigr) + \mathbf{1}_c,$$

where $\mathbf{1}_e$ is the indicator of edge $e$, and $w(A, e) = w(B, e) = w(X, e) = 0$ for $e \in \{a, b, c\}$. Then

$$f_2(M_x, X) = \alpha f_2(A, X) + (1 - \alpha) f_2(B, X) - \alpha (1 - \alpha) f_2(A, B) + \mathrm{MD}(\alpha, \ell_a, \ell_b, \ell_c),$$

where $f_2$ is the [f2 statistic](../patterson-s-f-statistics/f2.md) of the population frequencies and $\mathrm{MD}$ the [mixed drift](mixed-drift.md) (Lipson et al. 2013).

## Sources

- M. Lipson, P.-R. Loh, A. Levin, D. Reich, N. Patterson, B. Berger, *Efficient moment-based inference of admixture parameters and sources of gene flow*, Mol. Biol. Evol. 30 (2013), 1788–1802.
