# The invariant differential of a Weierstrass equation

Let $F$ be a field and let $E$ be the elliptic curve over $F$ given by a Weierstrass equation

$$W : \; y^2 + a_1 x y + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6, \qquad a_1, \dots, a_6 \in F,$$

with nonzero discriminant $\Delta_W$. Its **invariant differential** is

$$\omega_W = \frac{dx}{2y + a_1 x + a_3} = \frac{dy}{3x^2 + 2 a_2 x + a_4 - a_1 y},$$

a differential on $E$; the two expressions agree because the differential of the equation is
$(2y + a_1 x + a_3)\,dy = (3x^2 + 2a_2 x + a_4 - a_1 y)\,dx$.

**Theorem.**

1. $\omega_W$ is a regular differential on $E$ with no zeros, so it is a nonzero element of the line
   $H^0(E, \Omega^1_{E/F})$.
2. If the Weierstrass equation $W'$, with coefficients $a'_i$, is obtained from $W$ by the variable
   change $x = u^2 x' + r$, $y = u^3 y' + u^2 s x' + t$ with $u \in F^\times$ and $r, s, t \in F$, then
   $\Delta_{W'} = u^{-12} \Delta_W$ and $\omega_{W'} = u \, \omega_W$.
3. Hence the element
   $\beta_E = \Delta_W \, \omega_W^{\otimes 12}$ of $H^0(E, \Omega^1_{E/F})^{\otimes 12}$ is nonzero and
   does not depend on the Weierstrass equation $W$ of $E$.

## Depends on

- [Variable changes transform the Weierstrass equation](weierstrass-curves/equation-map-affine-coordinates-iff.md),
  for the variable changes between Weierstrass equations

## Proof depends on

- [Variable changes transform the Weierstrass equation](weierstrass-curves/equation-map-affine-coordinates-iff.md),
  for the substitution behind item 2: $dx = u^2 dx'$ and $2y + a_1 x + a_3 = u^3 (2y' + a'_1 x' + a'_3)$

## Expansion

This node is still to be broken down. A good expansion states and links:

- the transformation of the coefficients under a variable change, and with it
  $\Delta_{W'} = u^{-12} \Delta_W$ (Tate's formulary, to which Silverman refers for the invariance
  of $\beta$, p. 255);
- the regular differentials of a smooth projective curve, and the regularity and nonvanishing of
  $\omega_W$ on the affine part and at the point at infinity, for item 1.

## Sources

- J. H. Silverman, "Heights and elliptic curves", in G. Cornell and J. H. Silverman (eds.),
  *Arithmetic Geometry* (Storrs, 1984), Springer, New York, 1986, 253–265,
  <https://doi.org/10.1007/978-1-4613-8655-1_10>: p. 255, the meromorphic section
  $\beta = \Delta \cdot (dx / (2y + a_1 x + a_3))^{\otimes 12}$ and its invariance under the usual
  change of coordinates of a Weierstrass equation, with "Cf. the formulas in [14]", that is,
  J. Tate, "Algorithm for determining the type of a singular fiber in an elliptic pencil", in
  *Modular Functions of One Variable IV*, Lecture Notes in Mathematics 476, Springer, 1975, 33–52, as
  cited by Silverman.
- P. Deligne, "Preuve des conjectures de Tate et de Shafarevitch [d'après G. Faltings]", Séminaire
  Bourbaki, exposé 616 (1983/84), Astérisque 121–122 (1985), 25–41,
  <http://www.numdam.org/item/SB_1983-1984__26__25_0/>: Exemple 1.4, p. 28, the differential
  $dx/F_y = -dy/F_x$ for $F(x, y)$ the left side of
  $y^2 + a_1 x y + a_3 y - x^3 - a_2 x^2 - a_4 x - a_6 = 0$.
