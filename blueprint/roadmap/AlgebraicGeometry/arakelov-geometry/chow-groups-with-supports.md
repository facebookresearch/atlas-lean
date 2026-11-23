# Chow groups with supports and their products

This node is still to be broken down. It covers the algebraic intersection theory on which the
[arithmetic intersection product](arithmetic-intersection-product.md) rests: Chow groups with
supports, their products on regular schemes, and the moving lemmas used to bring cycles into proper
position.

Let $X$ be a noetherian scheme and $Y \subseteq X$ a closed subset. The group $Z^p_Y(X)$ of cycles of
codimension $p$ with supports in $Y$ is the free abelian group on the integral subschemes of $X$ of
codimension $p$ contained in $Y$, and the Chow group with supports $CH^p_Y(X)$ is its quotient by the
divisors $\operatorname{div}(f)$ of rational functions $f \in k(W)^\times$ on integral subschemes $W$
of codimension $p - 1$ contained in $Y$. There is an exact sequence
$CH^p_Y(X) \to CH^p(X) \to CH^p(X \setminus Y) \to 0$. For a family of supports $\Phi$, a family of
closed subsets stable under finite unions, $CH^p_\Phi(X)$ is the direct limit of the $CH^p_Y(X)$ over
$Y \in \Phi$. Gillet and Soulé state that, if $X$ is regular, there is an isomorphism
$CH^p_Y(X)_\mathbb{Q} \cong \mathrm{Gr}^p_\gamma K_0^Y(X)_\mathbb{Q}$ with the graded pieces of the
$\gamma$-filtration on $K$-theory with supports in $Y$. Through it the product of $K$-theory gives
products $CH^p_Y(X)_\mathbb{Q} \otimes CH^q_Z(X)_\mathbb{Q} \to CH^{p+q}_{Y \cap Z}(X)_\mathbb{Q}$
for all closed subsets $Y$ and $Z$, and, by taking limits, products for families of supports. For
cycles that intersect properly the product is given by Serre's Tor formula for intersection
multiplicities; for $X$ of finite type over a field it exists with integral coefficients.

A good expansion has pages for:

- Chow groups with supports in a closed subset and in a family of supports, with the exact sequence
  above (Gillet–Soulé, 4.1.1);
- $K$-theory with supports, its $\lambda$-operations and $\gamma$-filtration, and the isomorphism
  $CH^p_Y(X)_\mathbb{Q} \cong \mathrm{Gr}^p_\gamma K_0^Y(X)_\mathbb{Q}$ for regular noetherian $X$
  (Soulé, Theorem 4; Gillet and Soulé, "Intersection theory using Adams operations", Theorems 8.2
  and C);
- the products of Chow groups with supports on a regular scheme, and their agreement with Serre's Tor
  formula for cycles that intersect properly (Gillet and Soulé, Adams operations, Theorem C; Fulton,
  20.4; Serre, *Algèbre locale, multiplicités*);
- Chow's moving lemma for cycles on smooth quasi-projective varieties (Roberts), and Gillet and
  Soulé's moving lemma for $K_1$-chains on a smooth quasi-projective variety over an infinite field
  (4.2.6), which the proof of the arithmetic intersection product uses on the generic fibre.

## Sources

- H. Gillet and C. Soulé, "Arithmetic intersection theory", Publ. Math. IHÉS 72 (1990), 93–174,
  <http://www.numdam.org/item/PMIHES_1990__72__93_0/>: 4.1.1 (Chow groups with supports, the
  isomorphism with the graded $K$-theory with supports for regular $X$, products, Serre's Tor
  formula, families of supports, pp. 136–137), Remark 4.1.2 (integral coefficients over a field,
  p. 137), 4.2.6 (moving lemma for $K_1$-chains, pp. 142–143) and the uses of the moving lemma for
  cycles in 4.2.4–4.2.7.
- C. Soulé, "Opérations en K-théorie algébrique", Canad. J. Math. 37 (1985), 488–550: Theorem 4,
  as cited by Gillet and Soulé.
- H. Gillet and C. Soulé, "Intersection theory using Adams operations", Invent. Math. 90 (1987),
  243–278: Theorems 8.2 and C, as cited by Gillet and Soulé.
- J. Roberts, "Chow's moving lemma", in *Algebraic Geometry, Oslo 1970* (F. Oort, ed.),
  Wolters-Noordhoff, Groningen, 1972, 89–96.
- W. Fulton, *Intersection Theory*, Ergebnisse der Mathematik (3) 2, Springer, 1984: 20.4, as cited
  by Gillet and Soulé.
