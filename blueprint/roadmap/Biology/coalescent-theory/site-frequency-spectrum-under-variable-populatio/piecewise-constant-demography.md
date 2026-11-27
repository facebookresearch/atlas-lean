# Lineage counts and epoch lengths for piecewise-constant histories

For a piecewise-constant history with sizes $\nu_j$ on $[s_j, s_{j+1})$, the integrated intensity $\Lambda$ is piecewise linear with slope $1/\nu_j$ on piece $j$, and by the time-change representation $P(A^v_n(t) = k) = g_{nk}(\Lambda(t))$ of Tavaré (2004, Section 2.4), with $g_{nk}$ Tavaré's formula for the constant-size lineage count. On piece $j$, $\Lambda(t) = \Lambda(s_j) + (t - s_j)/\nu_j$, so the law of the number of lineages at the end of a piece is the constant-size transition semigroup $e^{(s_{j+1} - s_j)Q/\nu_j}$, with $Q$ the generator of Kingman's block-counting process, applied to its law at the start, and the laws at the change points compose by these matrix exponentials. Integrating over pieces gives the expected time with $k$ lineages,

$$E[T^v_k] = \sum_{j=0}^{K-1} \nu_j \int_{\Lambda(s_j)}^{\Lambda(s_{j+1})} g_{nk}(u)\, du,$$

with $\Lambda(s_K) = \infty$, a finite sum of exponentials in the $\Lambda(s_j)$ since each $g_{nk}$ is a linear combination of $e^{-\binom m2 u}$. Bhaskar and Song (2014) prove identifiability of piecewise-defined histories from the expected spectrum: the spectrum determines, up to a common positive factor, the means $c_m$ of the time to the first coalescence among $m$ of the sampled copies, $2 \le m \le n$ (their Lemma 1); these first-coalescence means determine piecewise-constant, piecewise-exponential and piecewise-generalized-exponential histories with $K$ pieces when $n \ge 2K$, $n \ge 4K - 1$ and $n \ge 6K - 2$ respectively (Corollaries 7–9); and, for the same sample sizes, the spectrum itself determines the history up to multiplying all change points and sizes by a common factor $\kappa > 0$, the rescaling of Lemma 10 (Theorem 11).

## Depends on

- [Clock and epoch lengths of the variable-size coalescent](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/deterministic-coalescent-time-change.md)
- [Piecewise-constant population-size history](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/piecewise-history.md)
- [Closed form of the first-coalescence times](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/choose-two-mul-first-coal-mean.md)
- [Tavaré's formula for the number of ancestral lineages](../../../Biology/coalescent-theory/ancestral-lineage-counting-and-tavar-s-formula/tavare-prob.md)
- [Generator of Kingman's block-counting process](../ancestral-lineage-counting-and-tavar-s-formula/block-counting-generator.md)

## Expansion

1. The piecewise-linear clock and its values at the change points.
2. The law of the lineage count at each change point as a product of matrix exponentials of the block-counting generator.
3. The occupation-time formula for $E[T^v_k]$ as a finite sum over pieces, and its closed form from Tavaré's formula.
4. The resulting exact expected spectrum for a piecewise-constant history.

## Sources

- S. Tavaré, Ancestral inference in population genetics, in *Lectures on Probability Theory and Statistics*, Lecture Notes in Math. 1837, Springer, 2004, 1–188, Sections 2.3 and 2.4.
- A. Bhaskar and Y. S. Song, Descartes' rule of signs and the identifiability of population demographic models from genomic variation data, Ann. Statist. 42 (2014), 2469–2493, Introduction, Lemmas 1 and 10, Corollaries 7–9 and Theorem 11. <https://arxiv.org/abs/1309.5056>
