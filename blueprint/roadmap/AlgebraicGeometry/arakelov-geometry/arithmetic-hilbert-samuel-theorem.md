# Arithmetic Hilbert–Samuel theorem

Let $X$ be an arithmetic variety of dimension $d + 1$ in the sense of Zhang (an integral scheme,
projective and flat over $\mathbb{Z}$), and let $\bar L$ and $\bar E$ be hermitian line bundles on
$X$. If $L_\mathbb{Q}$ is ample and $\bar L$ is relatively semipositive, then

$$\chi_{\sup}\bigl( \bar E \otimes \bar L^{\otimes N} \bigr) = \frac{(\bar L^{d+1})}{(d + 1)!} \,
N^{d+1} + o(N^{d+1}) \qquad (N \to \infty),$$

where $\chi_{\sup}$ is the logarithm of the volume of the unit ball of the sup norm on $H^0(X, E
\otimes L^{\otimes N}) \otimes \mathbb{R}$ divided by the covolume of the lattice $H^0(X, E \otimes
L^{\otimes N})$, and $(\bar L^{d+1})$ is the arithmetic self-intersection number of $\bar L$,
computed on a generic resolution when $X_\mathbb{Q}$ is singular. This is Zhang's form of the
theorem.

*Earlier forms.* Gillet and Soulé proved an $L^2$ form. Let $X$ be projective and flat over
$\mathbb{Z}$ of relative dimension $d$ with smooth generic fibre, $\bar L$ an ample line bundle with
a metric of positive curvature, invariant under complex conjugation, and choose a Kähler metric on
$X(\mathbb{C})$ invariant under complex conjugation, which defines $L^2$ norms. Let $\Lambda_n$ be
the image of $H^0(X, L^{\otimes n})$ in the real subspace $H^0(X(\mathbb{C}), L_\mathbb{C}^{\otimes
n})^+$ fixed by complex conjugation, that is, $H^0(X, L^{\otimes n})$ modulo torsion. Then

$$-\log \operatorname{covol}_{L^2}(\Lambda_n) = \frac{(\bar L^{d+1})}{(d + 1)!} \, n^{d+1} +
O(n^d \log n).$$

This is the case $E = L$, $\mathcal{F} = \mathcal{O}_X$ of their Theorem 8, an expansion for
symmetric powers of an ample hermitian vector bundle with metric positive in the sense of Griffiths,
equipped with the quotient metrics, twisted by a hermitian coherent sheaf. Their proof applies the
arithmetic Riemann–Roch theorem in its form for hermitian coherent sheaves over $\operatorname{Spec}
\mathbb{Z}$ to the hermitian coherent sheaves $\pi^* \mathcal{F} \otimes
\mathcal{O}_{\mathbb{P}(E)}(n)$, locally free on the generic fibre, on the projective bundle $\pi
\colon \mathbb{P}(E) \to X$, with the structure map $\mathbb{P}(E) \to \operatorname{Spec}
\mathbb{Z}$ ((36)–(38)); only a weak form of it is needed, the curvature of the Quillen metric
together with algebraic Riemann–Roch. It also uses the asymptotics of the analytic torsion of high
powers of a positive line bundle and the variation of the $L^2$ metrics (Bismut–Vasserot, Theorems 8
and 10).

Abbes and Bouche gave a direct proof. Let $K$ be a number field, $X \to \operatorname{Spec}
\mathcal{O}_K$ projective and flat with smooth generic fibre of dimension $r \ge 1$, and $L$ an
ample line bundle on $X$ with a hermitian metric of positive curvature at every infinite place, the
places being the embeddings of $K$ modulo complex conjugation. Let $B_n$ be the unit ball of the sup
norm on $W_n = H^0(X, L^{\otimes n}) \otimes_\mathbb{Z} \mathbb{R} = \bigoplus_\sigma W_{n,\sigma}$,
and $C_n$ the unit ball of the norm $\lVert x \rVert_2 = \sup_\sigma \lVert x_\sigma
\rVert_{2,\sigma}$, where $\lVert \cdot \rVert_{2,\sigma}$ is the $L^2$ norm at the place $\sigma$
for the volume form of the normalized curvature form, of total mass $1$; thus $C_n$ is a product of
placewise $L^2$ balls. Then both

$$\frac{(r + 1)!}{n^{r+1}} \Bigl( -\log \operatorname{covol} H^0(X, L^{\otimes n}) + \log
\operatorname{vol}(B_n) \Bigr) \quad \text{and} \quad \frac{(r + 1)!}{n^{r+1}} \Bigl( -\log
\operatorname{covol} H^0(X, L^{\otimes n}) + \log \operatorname{vol}(C_n) \Bigr)$$

converge, as $n \to \infty$, to the same limit $(L)^{r+1}$, which coincides with the arithmetic
self-intersection number of Gillet and Soulé. Their proof is an induction on the dimension through
the exact sequence of multiplication by a section of $L$, with an estimate of how far the volumes
are from being additive on that sequence. Zhang removes the smoothness of the generic fibre with a
generic resolution of singularities: he compares sup and $L^2$ norms by Gromov's inequality (1.5),
bounds the norms of a set of sections of maximal rank, independent sections spanning the rational
space obtained from integral multiples of finitely many generators, each of norm at most
$c^{\max(n_1, n_2)}$ in $\Gamma(f_{1*} L_1^{\otimes n_1} \otimes f_{2*} L_2^{\otimes n_2} \otimes
M)$, for projective morphisms $f_i \colon X_i \to X$, hermitian line bundles $L_i$ on $X_i$ with
$L_{i,\mathbb{Q}}$ ample and $M$ on $X$, and a constant $c$ independent of $n_1, n_2$ with
$\max(n_1, n_2) \ge 1$ (Lemma 1.6, p. 190, which prints the bound for all $n_1, n_2 \ge 0$; at $n_1
= n_2 = 0$ it would give norm at most $1$, false for $M = \mathcal{O}$ with $\lVert 1 \rVert = 2$,
whose nonzero integral sections have norm at least $2$), and compares the covolumes of lattices of
different ranks by Minkowski's theorem on successive minima, in a sandwich between models on a
generic resolution (Zhang, (1.5)–(1.8)).

*Small sections.* For a free $\mathbb{Z}$-module $M$ of rank $m$ with a norm on $M \otimes
\mathbb{R}$, Minkowski's theorem gives

$$\log \#\{ x \in M : \lVert x \rVert < 1 \} \ge \log \frac{\operatorname{vol}\{ x \in M \otimes
\mathbb{R} : \lVert x \rVert < 1 \}}{\operatorname{covol}(M)} - m \log 2;$$

Moriwaki's version for the closed unit ball has the error $-m \log 6$. Applied to $H^0(X, L^{\otimes
N})$ with the sup norm, whose rank is $\dim H^0(X_\mathbb{Q}, L_\mathbb{Q}^{\otimes N}) = O(N^d)$,
this gives $\log \#\{ s \in H^0(X, L^{\otimes N}) : \lVert s \rVert_{\sup} \le 1 \} \ge
\chi_{\sup}(\bar L^{\otimes N}) + O(N^d)$; so, under the hypotheses of the theorem,

$$\log \#\{ s \in H^0(X, L^{\otimes N}) : \lVert s \rVert_{\sup} \le 1 \} \ge
\frac{(\bar L^{d+1})}{(d + 1)!} \, N^{d+1} + o(N^{d+1}).$$

In particular, if $(\bar L^{d+1}) > 0$, then $H^0(X, L^{\otimes N})$ contains nonzero sections of
sup norm less than $1$ for all large $N$; for smooth generic fibre and positive curvature, Abbes and
Bouche's Corollaire states the existence of nonzero sections of sup norm at most $1$ and deduces it
from Minkowski's first theorem. For nef $\bar L$ the lower bound is an equality, see the
[Hilbert–Samuel formula for nef hermitian line bundles](arithmetic-volumes/arithmetic-hilbert-samuel-formula-for-nef-hermitian-line-bundles.md).

## Depends on

- [Arithmetic varieties and hermitian vector bundles](arithmetic-variety.md), for $\chi_{\sup}$ and the sup and $L^2$ norms
- [Arithmetic degree and arithmetic intersection numbers](arithmetic-intersection-numbers.md), for $(\bar L^{d+1})$
- [Positivity of hermitian line bundles](positivity-of-hermitian-line-bundles.md), for relative semipositivity

## Proof depends on

- [Arithmetic Riemann–Roch theorem](arithmetic-riemann-roch-theorem.md), in its form for hermitian coherent sheaves over $\operatorname{Spec} \mathbb{Z}$, (14)–(15), in Gillet and Soulé's proof of their Theorem 8 (5.1.3)
- [Analytic torsion and Quillen metrics](analytic-torsion-and-quillen-metrics.md), for the theorems of Bismut and Vasserot in the proof of Gillet and Soulé's Theorem 8
- [Gromov's inequality](gromov-inequality.md), in Zhang's proof (1.5)
- [Small elements of normed lattices](small-elements-of-normed-lattices.md), for Minkowski's theorems, in Zhang's proof (1.7) and in the paragraph on small sections
- [Resolution of singularities of quasi-projective varieties](../birational-geometry/resolution-of-singularities/resolution-of-singularities-of-quasi-projective-varieties.md), for the generic resolution by which Zhang removes the smoothness hypothesis (Zhang, (1.8); Abbes–Bouche, Remarques 4.3 (2))

## Sources

- S.-W. Zhang, "Positive line bundles on arithmetic varieties", J. Amer. Math. Soc. 8 (1995),
  187–221, author's scan of the printed edition
  <https://web.math.princeton.edu/~shouwu/publications/plav.pdf>: (1.2)–(1.3) (relative
  semipositivity, $\chi_{\sup}$), pp. 188–189; Theorem (1.4) (arithmetic Hilbert–Samuel formula),
  pp. 189–190, with its proof (1.5)–(1.8), pp. 190–193; Corollary (1.9) (small sections), p. 193.
- X. Yuan, "Big line bundles over arithmetic varieties", Invent. Math. 173 (2008), 603–649,
  arXiv:math/0612424 (version 2), <https://arxiv.org/abs/math/0612424v2>: "Theorem (Arithmetic
  Hilbert-Samuel)", p. 7 (Zhang's form with its hypotheses and history); Section 2.1
  ($\chi_{\sup}$), p. 8; Remark 2 after Definition 2.1, p. 10; Proposition 2.6 (1) with its proof,
  p. 13.
- H. Gillet and C. Soulé, "An arithmetic Riemann–Roch theorem", Invent. Math. 110 (1992), 473–543,
  <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0110>: 5.1.1 and Theorem 8, p. 534, with its
  proof in §§5.1.2–5.1.3, pp. 534–538 (the application of 4.1.5 on $\mathbb{P}(E)$, (36)–(38), pp.
  534–536; the remarks on the weak form of the Riemann–Roch theorem needed, p. 533 and after (47),
  p. 538).
- J.-M. Bismut and E. Vasserot, "The asymptotics of the Ray–Singer analytic torsion associated with
  high powers of a positive line bundle", Comm. Math. Phys. 125 (1989), 355–367: Theorem 8 and
  Theorem 10.
- A. Abbes and T. Bouche, "Théorème de Hilbert-Samuel « arithmétique »", Ann. Inst. Fourier 45
  (1995), 375–401, <http://www.numdam.org/item/AIF_1995__45_2_375_0/>: §1 (setting with $r \ge 1$,
  places, the norms $\lVert \cdot \rVert_2$), Théorème principal and Corollaire, pp. 375–376, proved
  in §3, pp. 380–389, and §4, pp. 390–396; Remarques 4.3, p. 396; §5 (comparison with the
  intersection theories).
- A. Moriwaki, "Continuity of volumes on arithmetic varieties", J. Algebraic Geom. 18 (2009),
  407–457, arXiv:math/0612269 (version 2), <https://arxiv.org/abs/math/0612269v2>: Proposition 2.1
  (1), p. 13.
