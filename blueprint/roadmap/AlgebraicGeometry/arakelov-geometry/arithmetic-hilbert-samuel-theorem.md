# Arithmetic Hilbert–Samuel theorem

Let $X$ be an arithmetic variety of dimension $d + 1$ in the sense of Zhang (an integral scheme,
projective and flat over $\mathbb{Z}$), and let $\bar L$ and $\bar E$ be hermitian line bundles on
$X$. If $L_\mathbb{Q}$ is ample and $\bar L$ is relatively semipositive, then
$$\chi_{\sup}\bigl( \bar E \otimes \bar L^{\otimes N} \bigr) = \frac{(\bar L^{d+1})}{(d + 1)!} \,
N^{d+1} + o(N^{d+1}) \qquad (N \to \infty),$$
where $\chi_{\sup}$ is the logarithm of the volume of the unit ball of the sup norm on
$H^0(X, E \otimes L^{\otimes N}) \otimes \mathbb{R}$ divided by the covolume of the lattice
$H^0(X, E \otimes L^{\otimes N})$, and $(\bar L^{d+1})$ is the arithmetic self-intersection number
of $\bar L$, computed on a generic resolution when $X_\mathbb{Q}$ is singular. This is Zhang's form
of the theorem.

*Earlier forms.* Gillet and Soulé proved an $L^2$ form for hermitian vector bundles. Let $X$ be
projective and flat over $\mathbb{Z}$ of relative dimension $d$ with smooth generic fibre, let
$\bar E = (E, h)$ be a hermitian vector bundle of rank $r$ with $E$ ample on $X$ and $h$ positive in
the sense of Griffiths, let $\bar{\mathcal{F}}$ be a hermitian coherent sheaf of rank $r'$, and
choose a Kähler metric on $X(\mathbb{C})$ invariant under complex conjugation. Put
$\chi_{L^2}(\mathcal{F} \otimes S^n E) = -\log \operatorname{vol}_{L^2}\bigl( H^0(X(\mathbb{C}),
\mathcal{F}_\mathbb{C} \otimes S^n E_\mathbb{C})^+ / H^0(X, S^n E \otimes \mathcal{F}) \bigr)$, the
volume being taken for the $L^2$ metric on the subspace $^+$ of elements fixed by complex
conjugation. Their Theorem 8 gives an expansion of $\chi_{L^2}(\mathcal{F} \otimes S^n E)$ with
leading term $r' \hat\sigma_{d+1}(\bar E) \, n^{d+r}$, followed by terms in $n^{d+r-1} \log n$ and
$n^{d+r-1}$ and an error $o(n^{d+r-1})$. For $E = L$ an ample line bundle with a metric of positive
curvature and $\mathcal{F} = \mathcal{O}_X$ with the trivial metric, $\hat\sigma_{d+1}(\bar L) =
(\bar L^{d+1}) / (d + 1)!$ and it gives
$$-\log \operatorname{vol}_{L^2}\bigl( H^0(X(\mathbb{C}), L_\mathbb{C}^{\otimes n})^+ /
H^0(X, L^{\otimes n}) \bigr) = \frac{(\bar L^{d+1})}{(d + 1)!} \, n^{d+1} + O(n^d \log n).$$
Their Theorem 9 compares, in the setting of Theorem 8, the number of sections of
$\mathcal{F} \otimes S^n E$ whose norm is at most $\exp\bigl( n (\hat\sigma_{d+1}(\bar E) -
\varepsilon) / \sigma_d(E) \bigr)$ at every point of $X(\mathbb{C})$, where
$\sigma_d(E) = p_*(s_d(E)) / (d + r - 1)!$ is built from the Segre class $s_d(E)$ and
$p \colon X \to \operatorname{Spec} \mathbb{Z}$, with a count of small linear forms on the dual
lattice: the logarithms of the two numbers differ by $r' \varepsilon n^{d+r} + O(n^{d+r-1} \log n)$.
Abbes and Bouche gave a direct proof. Let $K$ be a number field, $X \to \operatorname{Spec}
\mathcal{O}_K$ projective and flat with smooth generic fibre of dimension $r$, and $L$ an ample line
bundle on $X$ with a hermitian metric of positive curvature at every infinite place. Let $B_n$ be
the unit ball of the sup norm and $C_n$ that of the $L^2$ norm, taken for the volume form of the
normalized curvature form, on $H^0(X, L^{\otimes n}) \otimes_\mathbb{Z} \mathbb{R}$. Then both
$$\frac{(r + 1)!}{n^{r+1}} \Bigl( -\log \operatorname{covol} H^0(X, L^{\otimes n}) + \log
\operatorname{vol}(B_n) \Bigr) \quad \text{and} \quad \frac{(r + 1)!}{n^{r+1}} \Bigl( -\log
\operatorname{covol} H^0(X, L^{\otimes n}) + \log \operatorname{vol}(C_n) \Bigr)$$
converge, as $n \to \infty$, to the same limit $(L)^{r+1}$, which coincides with the arithmetic
self-intersection number of Gillet and Soulé. Their proof is an induction on the dimension through
the exact sequence of multiplication by a section of $L$, which measures how far the volumes are
from being additive on that sequence. Zhang removed the smoothness of the generic fibre by using a
desingularization of it.

*Small sections.* For a finitely generated free $\mathbb{Z}$-module $M$ of rank $m$ with a norm on
$M \otimes \mathbb{R}$, Minkowski's theorem gives
$$\log \#\{ x \in M : \lVert x \rVert < 1 \} \ge \log \frac{\operatorname{vol}\{ x \in M \otimes
\mathbb{R} : \lVert x \rVert < 1 \}}{\operatorname{covol}(M)} - m \log 2;$$
Moriwaki's version for the closed unit ball has the error $-m \log 6$. Applied to
$H^0(X, L^{\otimes N})$ with the sup norm, whose rank is $\dim H^0(X_\mathbb{Q},
L_\mathbb{Q}^{\otimes N}) = O(N^d)$, this gives
$\log \#\{ s \in H^0(X, L^{\otimes N}) : \lVert s \rVert_{\sup} \le 1 \} \ge
\chi_{\sup}(\bar L^{\otimes N}) + O(N^d)$; so, under the hypotheses of the theorem,
$$\log \#\{ s \in H^0(X, L^{\otimes N}) : \lVert s \rVert_{\sup} \le 1 \} \ge
\frac{(\bar L^{d+1})}{(d + 1)!} \, N^{d+1} + o(N^{d+1}).$$
In particular, if $(\bar L^{d+1}) > 0$, then $H^0(X, L^{\otimes N})$ contains nonzero sections of sup
norm less than $1$ for all large $N$; for smooth generic fibre and positive curvature, Abbes and
Bouche's Corollaire states the existence of nonzero sections of sup norm at most $1$ and deduces it
from Minkowski's first theorem. For nef $\bar L$ the lower
bound is an equality, see the
[Hilbert–Samuel formula for nef hermitian line bundles](arithmetic-hilbert-samuel-formula-for-nef-hermitian-line-bundles.md).

## Depends on

- [Arithmetic varieties and hermitian vector bundles](arithmetic-variety.md), for $\chi_{\sup}$ and the sup and $L^2$ norms
- [Arithmetic degree and arithmetic intersection numbers](arithmetic-intersection-numbers.md), for $(\bar L^{d+1})$
- [Positivity of hermitian line bundles](positivity-of-hermitian-line-bundles.md), for relative semipositivity

## Proof depends on

- [Arithmetic Riemann–Roch theorem](arithmetic-riemann-roch-theorem.md), in Gillet and Soulé's proof of their Theorem 8 (5.1.3), which applies the arithmetic Riemann–Roch theorem on a projective bundle
- [Analytic torsion and Quillen metrics](analytic-torsion-and-quillen-metrics.md), for the asymptotics of analytic torsion of Bismut and Vasserot in the proof of Gillet and Soulé's Theorem 8
- [Resolution of singularities of quasi-projective varieties](../birational-geometry/resolution-of-singularities-of-quasi-projective-varieties.md), for the desingularization of the generic fibre by which Zhang removes the smoothness hypothesis (Abbes–Bouche, Remarques 4.3 (2))

## Sources

- S.-W. Zhang, "Positive line bundles on arithmetic varieties", J. Amer. Math. Soc. 8 (1995),
  187–221, <https://www.ams.org/journals/jams/1995-08-01/S0894-0347-1995-1254133-7/>: (1.2)–(1.3)
  (relative semipositivity, $\chi_{\sup}$), Theorem (1.4) (arithmetic Hilbert–Samuel formula),
  Corollary (1.9) (small sections).
- X. Yuan, "Big line bundles over arithmetic varieties", Invent. Math. 173 (2008), 603–649,
  arXiv:math/0612424 (version 2), <https://arxiv.org/abs/math/0612424v2>: "Theorem (Arithmetic
  Hilbert-Samuel)", p. 7 (Zhang's form with its hypotheses and history); Section 2.1 ($\chi_{\sup}$),
  p. 8; Remark 2 after Definition 2.1 (Minkowski: $h^0(N\bar L) \ge \chi_{\sup}(N\bar L) +
  O(N^{n-1})$ for $\dim X = n$), p. 10; Proposition 2.6 (1) with its proof, p. 13.
- H. Gillet and C. Soulé, "An arithmetic Riemann–Roch theorem", Invent. Math. 110 (1992), 473–543,
  <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0110>: 5.1.1 and Theorem 8, p. 534, with the
  value of $\hat\sigma_{d+1}(\bar L)$ for a line bundle; Theorem 9 (small sections), p. 539.
- A. Abbes and T. Bouche, "Théorème de Hilbert-Samuel « arithmétique »", Ann. Inst. Fourier 45
  (1995), 375–401, <http://www.numdam.org/item/AIF_1995__45_2_375_0/>: §1, Théorème principal (sup
  and $L^2$ unit balls) and Corollaire, pp. 375–376, proved in §4, pp. 394–396; Remarques 4.3,
  p. 396; §5 (comparison with the intersection theories).
- A. Moriwaki, "Continuity of volumes on arithmetic varieties", J. Algebraic Geom. 18 (2009),
  407–457, arXiv:math/0612269 (version 2), <https://arxiv.org/abs/math/0612269v2>:
  Proposition 2.1 (1), p. 13.
