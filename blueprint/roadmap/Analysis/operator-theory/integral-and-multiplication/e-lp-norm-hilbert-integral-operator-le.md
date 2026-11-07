# An $L^p$ bound for Hilbert's integral operator

Let $p$ be a real number with
$p > 1$ and let $T$ be the operator on functions $g : \mathbb{R} \to \mathbb{R}$ given by

$$Tg(x) = \int_0^\infty \frac{g(y)}{x+y}\,dy \qquad (x \in \mathbb{R}).$$

Let $f : \mathbb{R} \to \mathbb{R}$ be continuous on $[0,\infty)$, compactly supported and zero
outside $[0,\infty)$, and put

$$C_p = \int_0^\infty \frac{dx}{x^{1/p}(1+x)}.$$

Then

$$\|Tf\|_{L^p([0,\infty))} \le C_p \, \|f\|_{L^p([0,\infty))},$$

where both norms are taken in $[0,\infty]$.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Integral, integro-differential, and pseudodifferential operators), `benchmark/level2/ma_proofbench_l2_29.lean` at openbmb/ma-proofbench@31bab4c.
