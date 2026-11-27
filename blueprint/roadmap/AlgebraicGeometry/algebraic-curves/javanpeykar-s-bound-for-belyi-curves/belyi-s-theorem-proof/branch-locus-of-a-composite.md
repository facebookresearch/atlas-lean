# Branch locus of a composite

Let $f \colon X \to Y$ and $g \colon Y \to Z$ be morphisms of schemes and $U \subset Z$ an open
subscheme. If the restriction $g^{-1}(U) \to U$ of $g$ is formally unramified and the restriction
$(g \circ f)^{-1}(U) \to g^{-1}(U)$ of $f$ is formally unramified, then the restriction $(g \circ
f)^{-1}(U) \to U$ of $g \circ f$ is formally unramified.

For finite morphisms of curves this is the inclusion $\operatorname{Crit}(g \circ f) \subset
\operatorname{Crit}(g) \cup g(\operatorname{Crit}(f))$ that Köck uses for the critical values:
if $g$ is unramified over the complement of a finite set $B_g$ of closed points of $Z$ and $f$ over
the complement of a finite set $B_f$ of closed points of $Y$, take $U = Z \setminus (B_g \cup
g(B_f))$, which is open because $g$, being finite, maps closed points to closed points; then
$g^{-1}(U) \subset Y \setminus B_f$, so $g \circ f$ is unramified over $U$.

The restriction of $g \circ f$ over $U$ is the composite of the two restrictions, and formally
unramified morphisms are stable under composition.

## Depends on

None among the pages.

## Proof depends on

None among the pages.

## Sources

- B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, <https://www.emis.de/ft/11086>, proof of Theorem 3.3, p. 262: "for any composition $g \circ f$ of morphisms
  between curves, we obviously have $\operatorname{Crit}(g \circ f) = \operatorname{Crit}(g) \cup
  g(\operatorname{Crit}(f))$". Only the inclusion is used.
