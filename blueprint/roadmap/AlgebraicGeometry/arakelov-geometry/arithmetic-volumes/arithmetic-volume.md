# Arithmetic volume

Let $X$ be a projective arithmetic variety of dimension $d + 1$ in the sense of Moriwaki (an
integral scheme, projective and flat over $\mathbb{Z}$, so that $X_\mathbb{Q}$ has dimension $d$),
and let $\bar L$ and $\bar N$ be hermitian line bundles on $X$; write $m\bar L + \bar N$ for $\bar
L^{\otimes m} \otimes \bar N$. The arithmetic volume of $\bar L$ is

$$\widehat{\mathrm{vol}}(\bar L) = \limsup_{m \to \infty} \frac{\log \#\{ s \in H^0(X, mL) :
\lVert s \rVert_{\sup} \le 1 \}}{m^{d+1} / (d + 1)!}.$$

It has the following properties.

1. *Finiteness.* There is a constant $C$ with $\log \#\{ s \in H^0(X, mL + N) : \lVert s
   \rVert_{\sup} \le 1 \} \le C m^{d+1}$ for all $m \ge 1$, so $\widehat{\mathrm{vol}}(\bar L)$ is a
   real number. If $\bar L$ is ample in Moriwaki's sense, then $\log \#\{ s \in H^0(X, mL + N) :
   \lVert s \rVert_{\sup} \le 1 \} = \frac{(\bar L^{d+1})}{(d + 1)!} m^{d+1} + o(m^{d+1})$, and
   hence $\widehat{\mathrm{vol}}(\bar L) = (\bar L^{d+1})$.
2. *Monotonicity.* Write $\bar L \le \bar M$ if there is an injective homomorphism $\varphi \colon L
   \to M$ with $\lVert \varphi(\cdot) \rVert_M \le \lVert \cdot \rVert_L$ on $X(\mathbb{C})$; then
   $\widehat{\mathrm{vol}}(\bar L) \le \widehat{\mathrm{vol}}(\bar M)$. The volume does not change
   if the sections of sup norm at most $1$ are replaced by those of sup norm less than $1$.
3. *Birational invariance.* If $\pi \colon X' \to X$ is a birational morphism of projective
   arithmetic varieties, then $\limsup_m m^{-(d+1)} \log \#\{ s \in H^0(X, mL + N) : \lVert s
   \rVert_{\sup} \le 1 \}$ equals the same expression for $\pi^*\bar L$ and $\pi^* \bar N$ on $X'$;
   in particular $\widehat{\mathrm{vol}}(\pi^* \bar L) = \widehat{\mathrm{vol}}(\bar L)$.
4. *Twisting.* $\limsup_m m^{-(d+1)} \log \#\{ s \in H^0(X, mL + N) : \lVert s \rVert_{\sup} \le 1
   \} = \widehat{\mathrm{vol}}(\bar L) / (d + 1)!$.
5. *Bigness.* The following are equivalent: $\widehat{\mathrm{vol}}(\bar L) > 0$; $\bar L$ is big;
   $\liminf_m m^{-(d+1)} \log \#\{ s \in H^0(X, mL) : \lVert s \rVert_{\sup} \le 1 \} > 0$;
   $\liminf_m m^{-(d+1)} \log \#\{ s \in H^0(X, mL) : \lVert s \rVert_{\sup} < 1 \} > 0$. The last
   condition is Yuan's definition of bigness, so it agrees with Moriwaki's. Moreover $\bar L$ is big
   if and only if for every hermitian line bundle $\bar M$ some $H^0(X, nL + M)$, $n \ge 1$, has a
   nonzero section of sup norm less than $1$; in particular, for big $\bar L$ and ample $\bar A$
   some $k \bar L - \bar A$ is strictly effective.
6. *Homogeneity.* $\widehat{\mathrm{vol}}(p \bar L) = p^{d+1} \widehat{\mathrm{vol}}(\bar L)$ for
   every integer $p \ge 0$. Hence $\widehat{\mathrm{vol}}$ extends to a function on
   $\widehat{\mathrm{Pic}}(X) \otimes \mathbb{Q}$, homogeneous of degree $d + 1$ for nonnegative
   rational factors, by $\widehat{\mathrm{vol}}(\bar L) = \widehat{\mathrm{vol}}(\bar M) / n^{d+1}$
   when $n\bar L$, for an integer $n > 0$, is represented by $\bar M$; and
   $\widehat{\mathrm{vol}}(\bar L) \le \widehat{\mathrm{vol}}(\bar M)$ when some positive multiples
   $n\bar L$ and $n\bar M$ are represented by hermitian line bundles $\bar L' \le \bar M'$.
7. *Progressions.* If $\bar L$ is big, then for every hermitian line bundle $\bar N$ and every
   integer $p \ge 1$ the $\limsup$, and also the $\liminf$, of $m^{-(d+1)} \log \#\{ s \in H^0(X, mL +
   N) : \lVert s \rVert_{\sup} \le 1 \}$ over all $m$ equal those over the multiples $m = pn$ of
   $p$.

Moriwaki writes $d$ for the absolute dimension of $X$, here $d + 1$. The estimate for ample $\bar L$
in 1 combines the [arithmetic Hilbert–Samuel theorem](../arithmetic-hilbert-samuel-theorem.md), the
estimates for [normed lattices](../small-elements-of-normed-lattices.md) and
[Zhang's ampleness theorem](../arithmetic-ampleness-theorem.md), which provides generating sections
of sup norm less than $1$ (Moriwaki, Lemma 3.1). The proof of 3 reduces to a finite $\pi$ and a
generically smooth $X'$ and again uses these theorems; 4 is deduced from 3, a generic resolution and
[Moriwaki's estimate for small sections along an ample divisor](moriwaki-fundamental-estimate.md)
(Theorem 4.3, through Theorem 3.4 and Lemma 3.6); 7 is Lemma 4.4; 5 and 6 follow from 4 and 7. The
characterization of bigness by small sections of $nL + M$ is Proposition 2.2 of Moriwaki's paper on
arithmetic height functions.

## Depends on

- [Arithmetic varieties and hermitian vector bundles](../arithmetic-variety.md)
- [Positivity of hermitian line bundles](../positivity-of-hermitian-line-bundles.md), for ample and big hermitian line bundles and hermitian $\mathbb{Q}$-line bundles
- [Arithmetic degree and arithmetic intersection numbers](../arithmetic-intersection-numbers.md), for $(\bar L^{d+1})$

## Proof depends on

- [Small elements of normed lattices](../small-elements-of-normed-lattices.md), for Moriwaki's Proposition 2.1, in Lemma 3.1 and in the proofs of 3 and 4
- [Moriwaki's estimate for small sections along an ample divisor](moriwaki-fundamental-estimate.md), for 4 (Theorem 4.3)
- [Arithmetic Hilbert–Samuel theorem](../arithmetic-hilbert-samuel-theorem.md), for the ample case of 1 (Moriwaki, Lemma 3.1 (1)) and the proof of 3 (Claim 4.2.1)
- [Zhang's arithmetic ampleness theorem](../arithmetic-ampleness-theorem.md), for generating sections of sup norm less than $1$ in Lemma 3.1 (1) and in the proof of 3 (Claim 4.2.1)
- [Resolution of singularities of quasi-projective varieties](../../birational-geometry/resolution-of-singularities/resolution-of-singularities-of-quasi-projective-varieties.md), for the generic resolutions used in the proofs of 3 and 4 (Theorems 4.2 and 4.3)

## Sources

- A. Moriwaki, "Continuity of volumes on arithmetic varieties", J. Algebraic Geom. 18 (2009),
  407–457, arXiv:math/0612269 (version 2), <https://arxiv.org/abs/math/0612269v2>: introduction
  (definition of $\widehat{\mathrm{vol}}$), p. 1; Conventions and terminology 8 (the order $\le$),
  p. 5; Proposition 2.1, p. 13; Lemma 3.1, pp. 15–16; Theorem 3.4, p. 19, and Lemma 3.6, p. 26;
  Section 4: definition, Proposition 4.1 (1) and (3), pp. 26–27, Theorem 4.2 (birational
  invariance), pp. 27–31, Theorem 4.3, p. 31, Lemma 4.4, p. 32, Theorem 4.5 ($\widehat{\mathrm{vol}} >
  0$ if and only if big) and Remark 4.6, pp. 33–34, Proposition 4.7 (homogeneity), p. 34; Lemmas 5.1
  and 5.2 (extension to $\widehat{\mathrm{Pic}}(X) \otimes \mathbb{Q}$ and monotonicity), p. 35.
- A. Moriwaki, "Arithmetic height functions over finitely generated fields", arXiv:math/9809016
  (version 2), <https://arxiv.org/abs/math/9809016v2>: Proposition 2.2, p. 7.
- X. Yuan, "Big line bundles over arithmetic varieties", Invent. Math. 173 (2008), 603–649,
  arXiv:math/0612424 (version 2), <https://arxiv.org/abs/math/0612424v2>: Definition 2.1, p. 10, and
  the Remark on p. 12 (the volume function).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a related formulation of the homogeneity 6 for positive integers, as
  `GlobalTheory.Published.VolHomog`.
