# Arithmetic intersection product

Let $X$ be an arithmetic variety over an arithmetic ring $A$ with fraction field $F$, and assume
that $X$ is regular, separated and of finite Krull dimension, and that its generic fibre $X_F$ is
quasi-projective. Then:

1. For all integers $p, q \ge 0$ there is a pairing

    $$\widehat{CH}^p(X) \otimes \widehat{CH}^q(X) \to \widehat{CH}^{p+q}(X)_\mathbb{Q}, \qquad
    \alpha \otimes \beta \mapsto \alpha\beta,$$

   uniquely determined by the following condition: if $Y$ and $Z$ are integral subschemes of $X$ of
   codimensions $p, q \ge 1$ that intersect properly on $X_F$, $g_Y$ and $g_Z$ are Green currents
   for $Y$ and $Z$, and $\alpha$ and $\beta$ are the classes of $([Y], g_Y)$ and $([Z], g_Z)$, then
   $\alpha\beta$ is the class of $([Y] \cdot [Z], g_Y * g_Z)$. A class of degree $0$ is a cycle of
   codimension $0$, that is, an integral combination of components of $X$, with Green current $0$,
   and it multiplies componentwise; for connected $X$ the class $(X, 0)$ is the unit.
2. After tensoring with $\mathbb{Q}$, this product makes $\widehat{CH}^*(X)_\mathbb{Q}$ a
   commutative and associative ring with unit, and $\zeta$ and $\omega$ are ring homomorphisms on
   the rationalized groups.
3. If $p = 1$ or $q = 1$, there is a unique pairing $\widehat{CH}^p(X) \otimes \widehat{CH}^q(X) \to
   \widehat{CH}^{p+q}(X)$ given by $([Y], g_Y) \cdot ([Z], g_Z) = ([Y] \cdot [Z], g_Y * g_Z)$ for
   cycles $Y$ and $Z$ that meet properly on all of $X$, and it induces the pairing of 1. For
   $\alpha, \beta \in \widehat{CH}^1(X)$ and $\gamma \in \widehat{CH}^q(X)$, $q \ge 0$, one has
   $\alpha\gamma = \gamma\alpha$ in $\widehat{CH}^{q+1}(X)$ and $\alpha(\beta\gamma) =
   \beta(\alpha\gamma)$ in $\widehat{CH}^{q+2}(X)$.

Here "intersect properly on $X_F$" means that $Y \cap Z \cap X_F$ is empty or of codimension $p + q$
in $X_F$; for cycles it is checked componentwise. The two components of $([Y] \cdot [Z], g_Y * g_Z)$
are defined as follows.

*The cycle part.* For a closed subset $T \subseteq X$, $CH^p_T(X)$ is the group of cycles of
codimension $p$ in $X$ supported in $T$ modulo the divisors of rational functions on integral
subschemes of codimension $p - 1$ contained in $T$. As $X$ is regular, separated, noetherian and of
finite Krull dimension (an assumption: regularity does not imply it, as Tanaka's excellent regular
noetherian domains of infinite dimension show, and Gillet and Soulé's arithmetic rings need not have
finite dimension), $CH^p_T(X)_\mathbb{Q}$ is isomorphic to the graded piece $\mathrm{Gr}^p_\gamma
K_0^T(X)_\mathbb{Q}$ of the $\gamma$-filtration on $K$-theory with supports in $T$, and the product
of $K$-theory gives products $CH^p_Y(X)_\mathbb{Q} \otimes CH^q_Z(X)_\mathbb{Q} \to CH^{p+q}_{Y \cap
Z}(X)_\mathbb{Q}$; for cycles that meet properly this product is given by Serre's Tor formula. Let
$\mathrm{fin}$ be the family of closed subsets of $X$ that do not meet $X_F$ and
$CH^p_{\mathrm{fin}}(X)$ the direct limit of the $CH^p_T(X)$ over $T \in \mathrm{fin}$. When $Y$ and
$Z$ intersect properly on $X_F$, $Y \cap Z$ lies in a closed subset whose intersection with $X_F$
has codimension at least $p + q$, and the product of the supported classes of $Y$ and $Z$ gives a
class $[Y] \cdot [Z]$ in $(Z^{p+q}(X_F) \oplus CH^{p+q}_{\mathrm{fin}}(X))_\mathbb{Q}$, a cycle on
$X_F$ and a class supported off $X_F$. Correspondingly $\widehat{CH}^{p+q}(X)$ is the quotient of
$\widehat{Z}^{p+q}(X_F) \oplus CH^{p+q}_{\mathrm{fin}}(X)$ by the relations attached to rational
functions $f$ on integral subschemes $W$ of codimension $p + q - 1$ of $X_F$: take the divisor of
$f$ on the closure $\overline W$ of $W$ in $X$, so that the relation consists of the arithmetic
divisor $(\operatorname{div}(f), -i_* \log |f|^2)$ on $X_F$ and the class of the vertical part of
$\operatorname{div}_{\overline W}(f)$ in $CH^{p+q}_{\mathrm{fin}}(X)$. For example, for $X =
\operatorname{Spec} \mathbb{Z}$ and $f = 2$ the relation is $(0, -\log 4) + [2]$; dropping the
vertical term would destroy the arithmetic degree. Thus $([Y] \cdot [Z], g_Y * g_Z)$ has a class in
$\widehat{CH}^{p+q}(X)_\mathbb{Q}$.

*The star product.* On the smooth quasi-projective complex variety $X_\infty$ the Green current
$g_Y$ of an integral subscheme $Y$ of positive codimension meeting $X_F$ is the class of a Green
form $\eta_Y$ of logarithmic type for $Y_\infty$ (a vertical $Y$ has $Y_\infty = \emptyset$); put
$\omega_Y = \delta_Y + dd^c g_Y$. For each irreducible component $Z_j$ of $Z_\infty$, not contained
in $Y_\infty$ since $Y$ and $Z$ intersect properly, choose a resolution of singularities $\widetilde
Z_j \to Z_j$, projective and birational, let $\psi_j \colon \widetilde Z_j \to X_\infty$ be its
composite with the inclusion, and set $g_Y \wedge \delta_{Z_j} = \psi_{j*}[\psi_j^* \eta_Y]$, which
does not depend on the resolution. Then

$$g_Y * g_Z = g_Y \wedge \delta_Z + \omega_Y \wedge g_Z \in
\widetilde{\mathcal{D}}^{p+q-1,p+q-1}(X_\mathbb{R}),$$

whose class depends only on the classes $g_Y$ and $g_Z$, and $dd^c(g_Y * g_Z) + \delta_{[Y] \cdot
[Z]} = \omega_Y \wedge \omega_Z$ on $X_\infty$; these are the properties of the star product of
[Green forms of logarithmic type](green-forms-of-logarithmic-type.md).

Gillet and Soulé's proof moves representatives into good position: the moving lemma for cycles on
the smooth quasi-projective $X_F$ (p. 143) and their moving lemma for $K_1$-chains (4.2.6), with
Lemmas 4.2.4 and 4.2.5, give representatives meeting properly on $X_F$ and show that the class of
the product does not depend on them; replacing a $K_1$-chain by an equivalent one uses the
comparison of the corresponding currents (3.3.5). For the integral pairing of 3 they move a Cartier
divisor away from finitely many generic points simultaneously, using the regular, hence factorial,
semilocal ring of $X$ at these points, not only its local rings one at a time (pp. 144–145).
Commutativity comes from that of the star product (2.2.9) and of the product of cycles. For
associativity Gillet and Soulé use the associativity of the star product on projective varieties
(Theorem 2.2.14): they first show that replacing representatives does not change the associativity
check, then choose Green currents for the closures of the cycles in a regular arithmetic variety
$\bar X$ containing $X$ as an open subscheme and with projective generic fibre, and restrict these
to $X$ (p. 144). Bost, Gillet and Soulé's associativity of the star product on smooth
quasi-projective varieties (Theorem 1.3.2 (ii)) gives associativity on $X$ directly; the
dependencies below follow this second route, which needs no compactification of $X$.

## Depends on

- [Arithmetic Chow groups](arithmetic-chow-group.md)
- [Chow groups with supports and their products](chow-groups-with-supports.md), for the Chow groups with supports $CH^p_T(X)$, $CH^p_{\mathrm{fin}}(X)$ and their products, which define the cycle part $[Y] \cdot [Z]$
- [Green forms of logarithmic type and the star product](green-forms-of-logarithmic-type.md), for the representatives $\eta_Y$ and the star product
- [Resolution of singularities of quasi-projective varieties](../birational-geometry/resolution-of-singularities/resolution-of-singularities-of-quasi-projective-varieties.md), for the resolutions $\widetilde Z_j \to Z_j$ through which $g_Y \wedge \delta_Z$ is defined
- [Arithmetic varieties and hermitian vector bundles](arithmetic-variety.md)

## Proof depends on

- [Chow groups with supports and their products](chow-groups-with-supports.md), for the moving lemma for cycles and for $K_1$-chains on $X_F$ (Gillet–Soulé 4.2.4–4.2.7)
- [Green forms of logarithmic type and the star product](green-forms-of-logarithmic-type.md), for the independence of choices, commutativity and associativity of the star product

## Sources

- H. Gillet and C. Soulé, "Arithmetic intersection theory", Publ. Math. IHÉS 72 (1990), 93–174,
  <http://www.numdam.org/item/PMIHES_1990__72__93_0/>: 1.3.2 and Theorem 1.3.5 (Green forms of
  logarithmic type, pp. 103–106), 2.1.3 ($g_Y \wedge \delta_Z$ and the star product, pp. 111–112),
  Theorem 2.1.4 (p. 112), Corollaries 2.2.9–2.2.11 with the Definition that follows them (the star
  product of Green currents, pp. 121–122), 4.1.1 (Chow groups with supports and their products, pp.
  136–137), 4.2.1 and 4.2.2 (pp. 137–138), Theorem 4.2.3 (pp. 138–139) with its proof 4.2.4–4.2.7
  (pp. 139–145; moving lemmas pp. 142–143, the integral pairing pp. 144–145), Theorem 4.2.9 (pp.
  145–146); Theorem 2.2.14, p. 123.
- J.-B. Bost, H. Gillet and C. Soulé, "Heights of projective varieties and positive Green forms", J.
  Amer. Math. Soc. 7 (1994), 903–1027: Proposition-Definition 1.3.1 and Theorem 1.3.2 (ii) (the star
  product on smooth quasi-projective varieties), pp. 919–920; §2.2, pp. 935–936.
- H. Tanaka, "Infinite dimensional excellent rings", arXiv:1706.02491 (version 2): Theorem 3.11, p. 10.
