# Gaudron–Rémond isogeny estimate

Let $k$ be a number field, $A$ an abelian variety of
dimension $g \ge 1$ over $k$ with stable Faltings height $h_F(A)$ (Faltings' normalization), and

$$\kappa(A) = \Bigl( (14 g)^{64 g^2} [k : \mathbb{Q}] \max\bigl(h_F(A), \log [k : \mathbb{Q}],
1\bigr)^2 \Bigr)^{1024 g^3}.$$

Let $K$ be any field extension of $k$ and $A'$ an abelian variety over $k$ such that $A_K$ and
$A'_K$ are isogenous. Then there are isogenies $\varphi_1 : A_K \to A'_K$ and
$\varphi_2 : A'_K \to A_K$ over $K$ whose degrees are at most $\kappa(A)$. The degree of an
isogeny is the rank of the finite flat morphism, which the statement bounds at every point of
the target.

## Informally uses

- [Isogeny estimate with auxiliary heights](isogeny-estimate-with-auxiliary-heights.md), for the
  bound $(9g)^{96 g^4} P^{2^{10} g^3}$ (Lemme 9.3), after the reduction to $k \subset K \subset k_1$:
  an isogeny defined over $K$ is defined over $K \cap k_1$ (p. 2097)
- [Field of definition of the endomorphisms of a product of isogenous abelian
  varieties](silverberg-field-of-definition.md), for the field $k_1$ of that reduction
- [Raynaud's estimate for the Faltings height under
  isogeny](../stable-faltings-height/raynaud-isogeny-height-estimate.md), item 1, for $h_F(A') \le
  h_F(A) + \frac{1}{2} \log Q$ when $Q$ bounds the degree of an isogeny $A \to A'$, and the same
  bound for $h_F(A'')$ and $h_F(A''')$ (Lemme 9.4, pp. 2100–2101), which removes these heights from
  $P$; with the elementary Lemme 8.5 (p. 2096), the resulting inequality for $M$ gives $\kappa(A)$
- [Isogeny degrees from last minima](isogeny-degree-from-last-minima.md), item 1, over $K$ and over
  $k_1$, for isogenies $A \to A''$ and $A \to A'''$ of degree at most $Q$ in Lemme 9.4
- [Bost's lower bound for the Faltings height](../stable-faltings-height/bost-lower-bound.md), for
  $h_F(A) \ge -\frac{3}{2} g$ in Lemme 9.4

## Sources

- É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057–2108, Théorème 1.4, p. 2060, with $\kappa(A)$ defined on p. 2058 and the degree of a pair of isogenies on p. 2059, <https://doi.org/10.1215/00127094-2782528>.
