# Arithmetic intersection product

Let $X$ be an arithmetic variety over an arithmetic ring $A$ with fraction field $F$, and assume
that $X$ is regular and that its generic fibre $X_F$ is quasi-projective. Then:

1. For all integers $p, q \ge 0$ there is a pairing
   $$\widehat{CH}^p(X) \otimes \widehat{CH}^q(X) \to \widehat{CH}^{p+q}(X)_\mathbb{Q}, \qquad
   \alpha \otimes \beta \mapsto \alpha\beta,$$
   uniquely determined by the following condition: if $Y$ and $Z$ are integral subschemes of $X$ of
   codimensions $p$ and $q$ that intersect properly on $X_F$, $g_Y$ and $g_Z$ are Green currents for
   $Y$ and $Z$, and $\alpha$ and $\beta$ are the classes of $([Y], g_Y)$ and $([Z], g_Z)$, then
   $\alpha\beta$ is the class of $([Y] \cdot [Z], g_Y * g_Z)$.
2. This product makes $\widehat{CH}^*(X)_\mathbb{Q}$ a commutative and associative ring.
3. If $p = 1$ or $q = 1$, there is a unique pairing $\widehat{CH}^p(X) \otimes \widehat{CH}^q(X)
   \to \widehat{CH}^{p+q}(X)$ given by $([Y], g_Y) \cdot ([Z], g_Z) = ([Y] \cdot [Z], g_Y * g_Z)$
   for cycles $Y$ and $Z$ that meet properly on all of $X$, and it induces the pairing of 1. For
   $\alpha, \beta \in \widehat{CH}^1(X)$ and $\gamma \in \widehat{CH}^q(X)$, $q \ge 0$, one has
   $\alpha\gamma = \gamma\alpha$ in $\widehat{CH}^{q+1}(X)$ and $\alpha(\beta\gamma) =
   \beta(\alpha\gamma)$ in $\widehat{CH}^{q+2}(X)$.

Here "intersect properly on $X_F$" means that $Y \cap Z \cap X_F$ is empty or of codimension
$p + q$ in $X_F$, and the two components of $([Y] \cdot [Z], g_Y * g_Z)$ are defined as follows.

*The cycle part.* For a closed subset $T \subseteq X$, $CH^p_T(X)$ is the group of cycles of
codimension $p$ supported in $T$ modulo the divisors of rational functions on integral subschemes of
codimension $p - 1$ contained in $T$. Since $X$ is regular, $CH^p_T(X)_\mathbb{Q}$ is isomorphic to
the graded piece $\mathrm{Gr}^p_\gamma K_0^T(X)_\mathbb{Q}$ of the $\gamma$-filtration on
$K$-theory with supports in $T$, and the product of $K$-theory gives products
$CH^p_Y(X)_\mathbb{Q} \otimes CH^q_Z(X)_\mathbb{Q} \to CH^{p+q}_{Y \cap Z}(X)_\mathbb{Q}$; for
cycles that meet properly this product is given by Serre's Tor formula. Let $\mathrm{fin}$ be the
family of closed subsets of $X$ that do not meet $X_F$ and $CH^p_{\mathrm{fin}}(X)$ the direct limit
of the $CH^p_T(X)$ over $T \in \mathrm{fin}$. When $Y$ and $Z$ intersect properly on $X_F$,
$[Y] \cdot [Z]$ defines a class in $(Z^{p+q}(X_F) \oplus CH^{p+q}_{\mathrm{fin}}(X))_\mathbb{Q}$,
and $\widehat{CH}^{p+q}(X)$ is the quotient of $\widehat{Z}^{p+q}(X_F) \oplus
CH^{p+q}_{\mathrm{fin}}(X)$ by the arithmetic divisors $\widehat{\operatorname{div}}(f)$ of rational
functions on integral subschemes of codimension $p + q - 1$ of $X_F$, so that the pair
$([Y] \cdot [Z], g_Y * g_Z)$ has a class in $\widehat{CH}^{p+q}(X)_\mathbb{Q}$.

*The star product.* On the smooth quasi-projective complex variety $X_\infty$, a Green current
$g_Y$ for $Y$ is represented by a Green form of logarithmic type, a smooth form on
$X_\infty \setminus Y_\infty$ that is locally integrable on $X_\infty$ and whose current is $g_Y$;
put $\omega_Y = \delta_Y + dd^c g_Y$. For each irreducible component $Z_j$ of $Z_\infty$ choose a
resolution of singularities $\widetilde Z_j \to Z_j$, projective and birational, let
$\psi_j \colon \widetilde Z_j \to X_\infty$ be its composite with the inclusion, and set
$g_Y \wedge \delta_{Z_j} = \psi_{j*}[\psi_j^* g_Y]$, which does not depend on the resolution. Then
$$g_Y * g_Z = g_Y \wedge \delta_Z + \omega_Y \wedge g_Z \in
\widetilde{\mathcal{D}}^{p+q-1,p+q-1}(X_\mathbb{R}),$$
which depends only on the Green currents $g_Y$ and $g_Z$, not on the forms representing them, and
satisfies $dd^c(g_Y * g_Z) + \delta_{[Y] \cdot [Z]} = \omega_Y \wedge \omega_Z$ on $X_\infty$. The
maps $\zeta$ and $\omega$ of the arithmetic Chow groups are ring homomorphisms for this product.

In Gillet and Soulé's proof (4.2.4–4.2.7) the moving lemma for cycles on $X_F$ moves
representatives until they meet properly on $X_F$, and Lemmas 4.2.5 and 4.2.6 show that the class
does not depend on the representatives. Commutativity, and associativity when $X_F$ is projective,
come from Lemma 4.2.4, which combines the commutativity and associativity of the star product
(2.2.9 and 2.2.14) with those of the product of cycles. When $X_F$ is only quasi-projective, they
embed $X$ as an open subscheme of
a regular scheme $\bar X$ whose generic fibre is projective, constructed by resolution of
singularities on the generic fibre, and deduce associativity on $X$ from associativity on $\bar X$.

## Depends on

- [Arithmetic Chow groups](arithmetic-chow-group.md)
- [Chow groups with supports and their products](chow-groups-with-supports.md), for the Chow groups with supports $CH^p_T(X)$, $CH^p_{\mathrm{fin}}(X)$ and their products, which define the cycle part $[Y] \cdot [Z]$
- [Resolution of singularities of quasi-projective varieties](../birational-geometry/resolution-of-singularities-of-quasi-projective-varieties.md), for the resolutions $\widetilde Z_j \to Z_j$ through which $g_Y \wedge \delta_Z$ is defined and for the Green forms of logarithmic type representing Green currents (Gillet–Soulé 1.3.5 and 2.1.3)

## Proof depends on

- [Chow groups with supports and their products](chow-groups-with-supports.md), for the moving lemma for cycles and for $K_1$-chains on $X_F$ (Gillet–Soulé 4.2.4–4.2.7)
- [Resolution of singularities of quasi-projective varieties](../birational-geometry/resolution-of-singularities-of-quasi-projective-varieties.md), for the regular scheme $\bar X \supseteq X$ with projective generic fibre used to prove associativity when $X_F$ is only quasi-projective (Gillet–Soulé 4.2.7)

## Sources

- H. Gillet and C. Soulé, "Arithmetic intersection theory", Publ. Math. IHÉS 72 (1990), 93–174,
  <http://www.numdam.org/item/PMIHES_1990__72__93_0/>: 1.3.2 and Theorem 1.3.5 (Green forms of
  logarithmic type, pp. 103–106), 2.1.3 ($g_Y \wedge \delta_Z$ and the star product, pp. 111–112),
  Theorem 2.1.4 (p. 112), Corollaries 2.2.9–2.2.11 with the Definition that follows them (the star
  product of Green currents, pp. 121–122), 4.1.1 (Chow groups with supports and their products,
  pp. 136–137), 4.2.1 and 4.2.2 (pp. 137–138), Theorem 4.2.3 (pp. 138–139) with its proof
  4.2.4–4.2.7 (pp. 139–145), Theorem 4.2.9 (pp. 145–146).
