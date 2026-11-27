# Green forms of logarithmic type and the star product

This node is still to be broken down: the statements below are precise, but their proofs are not.

Let $X$ be a smooth quasi-projective complex variety and $Y \subset X$ a closed analytic subset
containing no irreducible component of $X$. A smooth form $\eta$ on $X \setminus Y$ is of
*logarithmic type* along $Y$ if there are a projective morphism $\pi \colon \tilde X \to X$ from a
smooth variety, smooth over $X \setminus Y$, such that $\pi^{-1}(Y)$ is a divisor with normal
crossings, and a smooth form $\varphi$ on $\tilde X \setminus \pi^{-1}(Y)$ with $\eta = \pi_*
\varphi$, such that near every point of $\tilde X$ there are local coordinates $z_1, \dots, z_m$ in
which $\pi^{-1}(Y)$ is $z_1 \cdots z_k = 0$ and $\varphi = \sum_{i=1}^k \alpha_i \log |z_i|^2 +
\beta$ with smooth $\partial$- and $\bar\partial$-closed forms $\alpha_i$ and a smooth form $\beta$.
Such a form is locally integrable on $X$. For $Y$ irreducible of codimension $p > 0$, a *Green form
of logarithmic type* for $Y$ is a smooth real $(p-1, p-1)$-form $g_Y$ on $X \setminus Y$ of
logarithmic type along $Y$ such that $dd^c [g_Y] + \delta_Y$ is smooth; for example $-\log \lVert s
\rVert^2$ for $Y = \operatorname{div}(s)$, $p = 1$.

1. (Gillet–Soulé, Theorem 1.3.5.) Every closed irreducible subvariety $Y \subset X$ of positive
   codimension has a Green form of logarithmic type.
2. (Star product, Gillet–Soulé 2.1.3–2.1.4 and 2.2.9–2.2.11.) Let $g_Y$ be a Green form of
   logarithmic type for a cycle $Y$ of codimension $p$, put $\omega_Y = \delta_Y + dd^c g_Y$, and
   let $Z$ be a cycle of codimension $q$ with Green current $g_Z$ whose components are not contained
   in $|Y|$. For each component $Z_j$ choose a resolution of singularities $\tilde Z_j \to Z_j$, let
   $\psi_j \colon \tilde Z_j \to X$ be its composite with the inclusion, and put $g_Y \wedge
   \delta_{Z_j} = \psi_{j*} [\psi_j^* g_Y]$. Then $g_Y * g_Z = g_Y \wedge \delta_Z + \omega_Y \wedge
   g_Z$, and when $Y$ and $Z$ intersect properly $dd^c (g_Y * g_Z) + \delta_{Y \cdot Z} = \omega_Y
   \wedge \omega_Z$. When $Y$ and $Z$ intersect properly, the class of $g_Y * g_Z$ modulo
   $\operatorname{im} \partial + \operatorname{im} \bar\partial$ depends only on the classes of
   $g_Y$ and $g_Z$, and $g_Y * g_Z = g_Z * g_Y$ on these classes (Gillet–Soulé 2.2.9–2.2.11;
   Bost–Gillet–Soulé, Proposition–Definition 1.3.1 (ii) and Theorem 1.3.2 (i)). The one-sided
   condition that no component of $Z$ lies in $|Y|$ does not suffice: for a line $Y$ contained in a
   plane $Z$, $g_Y * g_Z$ is defined but $g_Z * g_Y$ is not.
3. (Associativity.) For cycles $Y$, $Z$, $W$ intersecting properly, pairwise and all together, $g_Y *
   (g_Z * g_W) = (g_Y * g_Z) * g_W$ modulo $\operatorname{im} \partial + \operatorname{im}
   \bar\partial$: Gillet and Soulé prove this when $X$ is projective (Theorem 2.2.14), Bost, Gillet
   and Soulé for smooth quasi-projective $X$ (Theorem 1.3.2 (ii)).
4. (Gillet–Soulé, Theorem 1.2.2 (i)–(ii), 1.2.3 and Lemma 1.2.4.) Let $M$ be a complex manifold, and
   let $\widetilde{A}^{p,q}(M)$ and $\widetilde{\mathcal{D}}^{p,q}(M)$ be the smooth forms and the
   currents of type $(p, q)$ on $M$ modulo $\operatorname{im} \partial + \operatorname{im}
   \bar\partial$. A current $\gamma$ with $\partial\bar\partial\gamma$ smooth is $\gamma = \omega +
   \partial\alpha + \bar\partial\beta$ with $\omega$ smooth and currents $\alpha$, $\beta$, and a
   smooth form $\omega = \partial u + \bar\partial v$ with currents $u$, $v$ is $\partial\alpha +
   \bar\partial\beta$ with smooth forms $\alpha$, $\beta$. Hence $\widetilde{A}^{p,q}(M) \to
   \widetilde{\mathcal{D}}^{p,q}(M)$ is injective, and any two Green currents for an analytic cycle
   $Y$ of codimension $p$ on $M$, classes $g \in \widetilde{\mathcal{D}}^{p-1,p-1}(M)$ of real
   currents with $dd^c g + \delta_Y$ smooth, differ by an element of $\widetilde{A}^{p-1,p-1}(M)$.

A good expansion has pages for:

- the local integrability and functoriality of forms of logarithmic type (Gillet–Soulé 1.3.3–1.3.4);
- the proof of item 1: first for a smooth $Y$ in a projective $X$ with surjective restriction maps
  on cohomology, by blowing up $Y$, then in general by an embedded modification making the inverse
  image of $Y$ a divisor with normal crossings, the $\partial\bar\partial$-lemma on a smooth
  projective compactification, and restriction to $X$ (Gillet–Soulé 1.3.6–1.3.9);
- the star product and its properties, items 2 and 3 (Gillet–Soulé §§2.1–2.2; Bost–Gillet–Soulé
  §1.3);
- the proof of item 4, from the equality of the $d$-, $\partial$- and $\bar\partial$-cohomology of
  currents and of smooth forms (Gillet–Soulé, proof of Theorem 1.2.2).

## Depends on

- [Poincaré–Lelong formula](../birational-geometry/poincare-lelong-formula.md), for currents of
  integration and the Green form $-\log \lVert s \rVert^2$ of a divisor
- [Resolution of singularities of quasi-projective varieties](../birational-geometry/resolution-of-singularities/resolution-of-singularities-of-quasi-projective-varieties.md),
  for the resolutions $\psi_j$ in the definition of the star product

## Proof depends on

- [Principalization of ideal sheaves in characteristic zero](../birational-geometry/resolution-of-singularities/principalization-of-ideal-sheaves.md),
  for the embedded modification in the proof of item 1
- [Resolution of singularities of quasi-projective varieties](../birational-geometry/resolution-of-singularities/resolution-of-singularities-of-quasi-projective-varieties.md),
  for the smooth projective compactification in the proof of item 1

## Sources

- H. Gillet and C. Soulé, "Arithmetic intersection theory", Publ. Math. IHÉS 72 (1990), 93–174,
  <http://www.numdam.org/item/PMIHES_1990__72__93_0/>: Theorem 1.2.2 (i) and (ii), p. 101, with its
  proof, pp. 101–102, 1.2.3, p. 102, and Lemma 1.2.4 (Green currents), pp. 102–103; Definition 1.3.2
  and 1.3.3–1.3.4 (forms of logarithmic type), pp. 103–105; 1.3.5 (Green forms of logarithmic type)
  and Theorem 1.3.5, p. 106, with its proof 1.3.6–1.3.9, pp. 106–109; 2.1.3 and Theorem 2.1.4 (star
  product), pp. 111–113; Corollaries 2.2.9–2.2.11 and Theorem 2.2.14, pp. 121–123.
- J.-B. Bost, H. Gillet and C. Soulé, "Heights of projective varieties and positive Green forms", J.
  Amer. Math. Soc. 7 (1994), 903–1027, archived publisher scan
  <https://web.archive.org/web/20170815232351id_/https://www.ams.org/journals/jams/1994-07-04/S0894-0347-1994-1260106-X/S0894-0347-1994-1260106-X.pdf>:
  Proposition-Definition 1.3.1 and Theorem 1.3.2, pp. 919–920.
