# Mallows' contraction of normalised sums

Let $G$ and $H$ be laws with finite second moments on a separable real Hilbert space. For $m \ge 1$ let $G^{(m)}$ be the law of

$$S_m(G) = m^{-1/2} \sum_{j=1}^m \bigl(Z_j(G) - E Z_j(G)\bigr)$$

for i.i.d. $Z_j(G) \sim G$, and similarly $H^{(m)}$. Then

$$d_2\bigl(G^{(m)}, H^{(m)}\bigr) \le d_2(G, H).$$

The law $G^{(m)}$ is the image under $x \mapsto m^{-1/2} x$ of the $m$-th [convolution power](conv-pow.md) of the law of $Z - EZ$; for $m = 0$ both normalised laws are the Dirac mass at $0$ and the inequality is trivial. Bickel and Freedman state (2.2) on the real line, citing Lemma 3 of Mallows (1972), and point to their Lemmas 8.7 and 8.8 and the scaling (8.2); this route works in any separable Hilbert space.

This is the step that makes the bootstrap of the mean work: if $F_n$ is close to $F$ in $d_2$, then the bootstrap law $F_n^{(m)}$ is close to $F^{(m)}$ uniformly in $m$, and $F^{(m)}$ is close to a normal law by the central limit theorem ([bootstrap central limit theorem](bootstrap-mean-tendsto-gaussian-real.md)).

## Informally uses

- [Centring decreases the Mallows metric](transport-cost-two-center-add-le.md): Lemma 8.8, to centre the summands.
- [Mallows metric of convolution powers](transport-cost-two-conv-pow-le.md): Lemma 8.7 for the $m$ summands.
- [Scaling of the Mallows metric](wasserstein-map-smul.md): (8.2), for the factor $m^{-1/2}$.

## Sources

- P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217, equation (2.2).
- C. L. Mallows, "A note on asymptotic joint normality", *Ann. Math. Statist.* 43 (1972) 508–515, Lemma 3, as cited by Bickel and Freedman.
