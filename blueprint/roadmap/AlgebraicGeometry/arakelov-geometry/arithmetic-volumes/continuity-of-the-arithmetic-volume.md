# Continuity of the arithmetic volume

Let $X$ be a projective arithmetic variety in the sense of Moriwaki and let $\bar L$ and $\bar A$ be
hermitian $\mathbb{Q}$-line bundles on $X$, that is, elements of $\widehat{\mathrm{Pic}}(X) \otimes
\mathbb{Q}$. Then

$$\lim_{\varepsilon \in \mathbb{Q},\ \varepsilon \to 0} \widehat{\mathrm{vol}}(\bar L +
\varepsilon \bar A) = \widehat{\mathrm{vol}}(\bar L).$$

More generally, for hermitian $\mathbb{Q}$-line bundles $\bar A_1, \dots, \bar A_n$ on $X$,
$\widehat{\mathrm{vol}}(\bar L + \varepsilon_1 \bar A_1 + \dots + \varepsilon_n \bar A_n) \to
\widehat{\mathrm{vol}}(\bar L)$ as the rational numbers $\varepsilon_1, \dots, \varepsilon_n$ tend
to $0$.

Moriwaki's proof first treats $n = 1$. By birational invariance he may replace $X$ by a generic
resolution of singularities and assume $X$ generically smooth; comparing $\bar L \pm \varepsilon
\bar A$ with $\bar L \pm \varepsilon \bar B$ and $\bar L \pm \varepsilon(\bar A + \bar B)$ for an
ample $\bar B$ with $\bar A + \bar B$ ample, by monotonicity of the volume, he may assume $\bar A$
ample; by homogeneity he may assume that $\bar L$ and $\bar A$ are hermitian line bundles and that
$\bar A$ satisfies the hypotheses of his Theorem 3.4, a multiple of an ample hermitian line bundle
doing so by Lemma 3.6 when $\dim X \ge 2$.
[Moriwaki's estimate for small sections along an ample divisor](moriwaki-fundamental-estimate.md)
(Theorem 3.4; when $\dim X = 1$, Proposition 3.5, over the normalization, an integral domain finite
and flat over $\mathbb{Z}$, after passing to tensor powers to make the modules free) gives constants
$C$, $D$ and $a_0$, depending only on $X$, $\bar L$ and $\bar A$, with

$$\hat h^0\bigl( a\bar L + (b - c)\bar A \bigr) \le \hat h^0\bigl( a\bar L - c\bar A \bigr) + C b
a^{\dim X - 1} + D a^{\dim X - 1} \log a$$

for all integers $a \ge b \ge c \ge 0$ with $a \ge a_0$, where $\hat h^0$ is the logarithm of the
number of sections of sup norm at most $1$. Taking $(a, b, c) = (pm, m, 0)$ and $(pm, m, m)$ and
letting $m \to \infty$ gives a constant $C'$ with $\widehat{\mathrm{vol}}(\bar L) \le
\widehat{\mathrm{vol}}(\bar L + \frac1p \bar A) \le \widehat{\mathrm{vol}}(\bar L) + \frac{C'}{p}$
and $\widehat{\mathrm{vol}}(\bar L - \frac1p \bar A) \le \widehat{\mathrm{vol}}(\bar L) \le
\widehat{\mathrm{vol}}(\bar L - \frac1p \bar A) + \frac{C'}{p}$ for all $p \ge 1$. The general case
follows by bounding each $\bar A_i$ between $-\bar B$ and $\bar B$ for one ample $\bar B$.

## Depends on

- [Arithmetic volume](arithmetic-volume.md), for $\widehat{\mathrm{vol}}$ on $\widehat{\mathrm{Pic}}(X) \otimes \mathbb{Q}$
- [Arithmetic varieties and hermitian vector bundles](../arithmetic-variety.md)

## Proof depends on

- [Moriwaki's estimate for small sections along an ample divisor](moriwaki-fundamental-estimate.md), for Theorem 3.4, Proposition 3.5 and Lemma 3.6
- [Arithmetic volume](arithmetic-volume.md), for birational invariance (Theorem 4.2), monotonicity and homogeneity (Lemmas 5.1 and 5.2)
- [Resolution of singularities of quasi-projective varieties](../../birational-geometry/resolution-of-singularities/resolution-of-singularities-of-quasi-projective-varieties.md), for the generic resolution of singularities that reduces the theorem to a generically smooth $X$

## Sources

- A. Moriwaki, "Continuity of volumes on arithmetic varieties", J. Algebraic Geom. 18 (2009),
  407–457, arXiv:math/0612269 (version 2), <https://arxiv.org/abs/math/0612269v2>: Theorem 5.4
  (continuity of volume) with its proof, pp. 36–38; Theorem 3.4 with its proof, pp. 19–25; Lemma
  3.6, p. 26; Corollary 1.1.2 (Gromov's inequality), p. 8; Lemma 3.1, pp. 15–16; introduction, p. 1.
