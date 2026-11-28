# Arithmetic Hilbert–Samuel formula for nef hermitian line bundles

Let $X$ be a projective arithmetic variety of dimension $d + 1$ in the sense of Moriwaki, and let
$\bar L$ and $\bar N$ be hermitian line bundles on $X$. If $\bar L$ is nef, then

$$\log \#\{ s \in H^0(X, mL + N) : \lVert s \rVert_{\sup} \le 1 \} = \frac{(\bar L^{d+1})}{(d +
1)!} \, m^{d+1} + o(m^{d+1}) \qquad (m \to \infty).$$

In particular $\widehat{\mathrm{vol}}(\bar L) = (\bar L^{d+1})$, so $(\bar L^{d+1}) \ge 0$ since the
volume is nonnegative, and $\bar L$ is big if and only if $(\bar L^{d+1}) > 0$.

Moriwaki states this as his Corollary 5.5, Theorem A of the introduction, writing $d$ for the
absolute dimension of $X$. For an ample hermitian line bundle $\bar A$, $\bar L + \varepsilon \bar A$
is ample for every rational $\varepsilon > 0$ since $\bar L$ is nef (Moriwaki, proof of
Corollary 5.5), so $\widehat{\mathrm{vol}}(\bar L + \varepsilon \bar A) = ((\hat c_1(\bar L) +
\varepsilon \hat c_1(\bar A))^{d+1})$ by the ample case of the
finiteness of the volume and homogeneity; letting $\varepsilon \to 0$, the continuity of the volume
gives $\widehat{\mathrm{vol}}(\bar L) = (\bar L^{d+1})$. If $\bar L$ is not big, both sides of the
asymptotic formula are then $o(m^{d+1})$ by the twisting property of the volume. If $\bar L$ is big,
some $k \bar L - \bar A$ is strictly effective (property 5 of the volume), $p\bar L - (k\bar L -
\bar A)$ is ample for $p \ge k$, and the ample case, along multiples of $p$ and then along all $m$ by
the comparison of limits over progressions (property 7, Moriwaki's Lemma 4.4), gives the lower bound
for the $\liminf$ after $p \to \infty$, while the twisting property gives the upper bound for the
$\limsup$.

## Depends on

- [Positivity of hermitian line bundles](../positivity-of-hermitian-line-bundles.md), for nef and big hermitian line bundles
- [Arithmetic degree and arithmetic intersection numbers](../arithmetic-intersection-numbers.md), for $(\bar L^{d+1})$
- [Arithmetic volume](arithmetic-volume.md), for $\widehat{\mathrm{vol}}$
- [Arithmetic varieties and hermitian vector bundles](../arithmetic-variety.md)

## Proof depends on

- [Continuity of the arithmetic volume](continuity-of-the-arithmetic-volume.md)
- [Arithmetic volume](arithmetic-volume.md), for the ample case of Lemma 3.1, Theorem 4.3, the effectivity of some $k \bar L - \bar A$ for big $\bar L$, Lemma 4.4 and homogeneity
- [Arithmetic Hilbert–Samuel theorem](../arithmetic-hilbert-samuel-theorem.md), through the ample case of Lemma 3.1 applied to $\bar L + \varepsilon \bar A$ and to $p \bar L - (k \bar L - \bar A)$
- [Ampleness of nef plus ample hermitian line bundles](../ampleness-of-nef-plus-ample-hermitian-line-bundles.md), for the ampleness of $\bar L + \varepsilon \bar A$ and of $p \bar L - (k \bar L - \bar A) = (p - k) \bar L + \bar A$ for nef $\bar L$ and ample $\bar A$ (Moriwaki, proof of Corollary 5.5)

## Sources

- A. Moriwaki, "Continuity of volumes on arithmetic varieties", J. Algebraic Geom. 18 (2009),
  407–457, arXiv:math/0612269 (version 2), <https://arxiv.org/abs/math/0612269v2>: Theorem A,
  p. 2, and Corollary 5.5 (arithmetic Hilbert–Samuel formula for nef hermitian line bundles) with its
  proof, pp. 38–39; Lemma 4.4, pp. 32–33.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result, as `GlobalTheory.Published.ArithHilbertSamuel`, and its consequence $\widehat{\mathrm{vol}}(\bar L) = (\bar L^{d+1})$ as `GlobalTheory.Published.VolNef`.
