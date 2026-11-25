# Height of a cycle

Let $X$ be a proper flat scheme over $\mathbb{Z}$ and $\bar L$ a hermitian line bundle on $X$. For
an integer $p \ge 0$ and a cycle $Z \in Z_p(X)$ of dimension $p$, the dimension being that of a
subscheme of $X$, the height of $Z$ with respect to $\bar L$ is the real number

$$h_{\bar L}(Z) = \widehat{\deg}\bigl( \hat c_1(\bar L)^p \mid Z \bigr),$$

the arithmetic degree of $Z$ with respect to $p$ copies of $\bar L$, given by Chambert-Loir's
characterization of arithmetic degrees of cycles. Bost, Gillet and Soulé define the same number by
formula (3.1.1) for a regular projective arithmetic variety $X$ over $\mathcal{O}_K$, pairing the
arithmetic class $\hat c_1(\bar L)^p$ with the ordinary cycle $Z$, and extend it to their arithmetic
varieties (flat and quasi-projective over $\mathcal{O}_K$ with regular generic fibre) for cycles
whose support is proper over $\mathcal{O}_K$; on these common domains, with invariant metrics, the
numbers agree. A cycle flat over $\mathbb{Z}$ has generic fibre of dimension $p - 1$. For a closed
point $z$, $h_{\bar L}(z) = \log \# \kappa(z)$. If $Z$ is integral and lies over a prime $\ell$,
then $h_{\bar L}(Z) = \deg\bigl( c_1(L|_{X_{\mathbb{F}_\ell}})^p \mid Z \bigr) \log \ell$. If $Z$ is
the Zariski closure of a closed point $z$ of $X_\mathbb{Q}$, with residue field $K = \kappa(z)$,
then $Z$ is the image of the morphism $\varepsilon_z \colon \operatorname{Spec} \mathcal{O}_K \to X$
extending $z$ and $h_{\bar L}(Z) = \widehat{\deg}(\varepsilon_z^* \bar L)$ is the arithmetic degree
of a hermitian line bundle on $\operatorname{Spec} \mathcal{O}_K$, not divided by $[K :
\mathbb{Q}]$.

*Projection formula.* For a morphism $f \colon X' \to X$ as in the projection formula for arithmetic
degrees (generically finite, or of projective arithmetic varieties with regular generic fibres) and
an integral cycle $Z$ on $X'$, $h_{f^* \bar L}(Z) = h_{\bar L}(f_* Z)$, where $f_* Z = [\kappa(Z) :
\kappa(f(Z))] f(Z)$ if $\dim f(Z) = \dim Z$ and $f_* Z = 0$ otherwise; for generically finite $f$
this follows from Chambert-Loir's Proposition (2.9), and for projective arithmetic varieties with
invariant metrics it is formula (3.2.1) of Bost, Gillet and Soulé.

*Normalized height.* Chambert-Loir normalizes the height by the degree. Write $X =
\mathcal{X}_\mathbb{Q}$ and $L = \mathcal{L}_\mathbb{Q}$ for a proper flat scheme $\mathcal{X}$ over
$\mathbb{Z}$ with a hermitian line bundle $\bar{\mathcal{L}}$. For a closed integral subscheme $Z$
of $X$ of dimension $d$, with Zariski closure $\mathcal{Z}$ in $\mathcal{X}$, of dimension $d + 1$,
put $\deg_L(Z) = \deg(c_1(L)^d \mid Z)$; when $\deg_L(Z) \ne 0$, which holds for every $Z$ when $L$
is ample, the normalized height is

$$h^{\mathrm{norm}}_{\bar{\mathcal{L}}}(Z) =
\frac{\widehat{\deg}\bigl( \hat c_1(\bar{\mathcal{L}})^{d+1} \mid \mathcal{Z} \bigr)}
{(d + 1) \deg_L(Z)} = \frac{h_{\bar{\mathcal{L}}}(\mathcal{Z})}{(d + 1) \deg_L(Z)}.$$

Chambert-Loir writes $h_{\bar{\mathcal{L}}}(Z)$ for this normalized height, a different
normalization of the unnormalized height $h_{\bar{\mathcal{L}}}(\mathcal{Z})$; Bost, Gillet and
Soulé use yet another normalization, dividing by the degree $[K' : \mathbb{Q}]$ of a field of
definition. The function $x \mapsto h^{\mathrm{norm}}_{\bar{\mathcal{L}}}([x])$ on
$X(\overline{\mathbb{Q}})$, where $[x]$ is the Zariski closure of $x$ in $X$, is a height function
relative to $L$ in the sense of Weil. If $f \colon \mathcal{X}' \to \mathcal{X}$ is a generically
finite morphism of proper flat schemes over $\mathbb{Z}$, $L$ is ample, and $Z$ is a closed integral
subscheme of $\mathcal{X}'_\mathbb{Q}$ with $\dim f(Z) = \dim Z$, then $\deg_{f^*L}(Z) > 0$ and
$h^{\mathrm{norm}}_{f^* \bar{\mathcal{L}}}(Z) = h^{\mathrm{norm}}_{\bar{\mathcal{L}}}(f(Z))$: by the
projection formula above and its analogue for geometric degrees, $f_*(c_1(f^* L)^d \cap [Z]) =
c_1(L)^d \cap f_*[Z]$ for proper $f$ (Stacks Project, Tag 02SU; the
[projection formula for intersection numbers](../birational-geometry/intersection-numbers-of-nef-line-bundles.md),
item 5), numerator and denominator are both multiplied by $[\kappa(Z) : \kappa(f(Z))]$.

*Projective space.* On $\mathbb{P}^N_\mathbb{Z}$, give $\mathcal{O}(1)$ the Fubini–Study metric: if
$s_f$ is the section defined by a homogeneous linear form $f$ in $T_0, \dots, T_N$ and $x = [x_0 :
\dots : x_N] \in \mathbb{P}^N(\mathbb{C})$, then $\lVert s_f \rVert(x) = |f(x_0, \dots, x_N)| /
(|x_0|^2 + \dots + |x_N|^2)^{1/2}$. The height $h_{\overline{\mathcal{O}(1)}}$ of cycles of
$\mathbb{P}^N_\mathbb{Z}$ for this metric is the height introduced by Faltings, the height of Bost,
Gillet and Soulé's §3 for the trivial hermitian bundle of rank $N + 1$; it differs from their
projective height of §4, defined with the Chern classes of the canonical quotient bundle. Its
relation with the heights of Chow forms is the subject of the node
[heights of Chow forms](heights-of-chow-forms.md). For points it is not the logarithmic Weil height
with the maximum norm at infinity: for $[1 : 1] \in \mathbb{P}^1(\mathbb{Q})$ the archimedean
contribution is $\frac12 \log 2$, not $0$.

## Depends on

- [Arithmetic degree and arithmetic intersection numbers](arithmetic-intersection-numbers.md), for the arithmetic degrees $\widehat{\deg}(\hat c_1(\bar L)^p \mid Z)$
- [Arithmetic varieties and hermitian vector bundles](arithmetic-variety.md)

## Proof depends on

- [Intersection numbers and Riemann–Roch for nef line bundles](../birational-geometry/intersection-numbers-of-nef-line-bundles.md),
  for the projection formula 5 for geometric degrees
- [Arithmetic degree and arithmetic intersection numbers](arithmetic-intersection-numbers.md), for
  the projection formula for arithmetic degrees, from which the projection formula for heights
  follows (Chambert-Loir, Proposition (2.9); Bost–Gillet–Soulé, (3.2.1))

## Sources

- J.-B. Bost, H. Gillet and C. Soulé, "Heights of projective varieties and positive Green forms", J.
  Amer. Math. Soc. 7 (1994), 903–1027, archived publisher scan
  <https://web.archive.org/web/20170815232351id_/https://www.ams.org/journals/jams/1994-07-04/S0894-0347-1994-1260106-X/S0894-0347-1994-1260106-X.pdf>:
  introduction, pp. 904–905; §2.1.1, p. 930 (their arithmetic varieties); Proposition 2.3.1, pp.
  937–939 (the pairing of arithmetic classes with cycles); definition (3.1.1) for a regular
  projective arithmetic variety, p. 945, and its extension to cycles with support proper over $S$,
  p. 946; 3.1.2.1–3.1.2.3 (examples; Faltings's height, from G. Faltings, "Diophantine approximation
  on abelian varieties", Ann. of Math. (2) 133 (1991), 549–576), pp. 946–947; §3.1.4 (their
  normalized height), p. 948; Proposition 3.2.1 (iii), formula (3.2.1), and the Remark that follows,
  p. 949; Definition 4.1.1 and Proposition 4.1.2 (the projective height), pp. 964–965.
- A. Chambert-Loir, "Arakelov geometry, heights, equidistribution, and the Bogomolov conjecture",
  arXiv:1904.05630v3 (2020), <https://arxiv.org/abs/1904.05630v3>: Theorem (2.5) and Examples (2.7)
  and (2.8), pp. 3–4; Proposition (2.9), pp. 4–5; Definition (3.3) and Proposition (3.4), p. 5, with
  the proof of (3.4) and Example (3.5), p. 6; Example (5.2) (the metric on $\mathcal{O}(1)$), p. 12.
- The Stacks Project, <https://stacks.math.columbia.edu>: Tag 02SU (projection formula for first
  Chern classes and proper push-forward).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses heights of cycles, with their existence, recursive characterization and projection formula
  for cycles generically finite onto their image, as `GlobalTheory.Published.CycleHeights`.
