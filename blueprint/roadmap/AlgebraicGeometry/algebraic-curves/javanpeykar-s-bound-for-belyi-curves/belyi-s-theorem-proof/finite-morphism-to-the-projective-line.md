# A curve has a finite morphism to the projective line

Let $k$ be a field and $C$ a curve over $k$, that is, a $k$-scheme that is proper, smooth of
relative dimension $1$ and geometrically irreducible. Then there is a finite morphism $C \to
\mathbb{P}^1_k$ over $k$.

## Depends on

None among the pages.

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

This node is still to be broken down. A good expansion states and links:

- a transcendental element $t$ of the function field $k(C)$, which has transcendence degree $1$
  over $k$, so that $k(t) \subset k(C)$ is a finite extension;
- the equivalence between finitely generated extensions of $k$ of transcendence degree $1$ and
  nonsingular projective curves with nonconstant morphisms (Stacks, Theorem 53.2.6), which turns
  $k(t) \subset k(C)$ into a nonconstant morphism $C \to \mathbb{P}^1_k$, the projective line
  being the nonsingular projective curve with function field $k(t)$;
- the finiteness of a morphism from a proper curve to a separated scheme that is nonconstant on
  every component of dimension $1$ (Stacks, Lemma 53.2.4).

## Sources

- B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, <https://www.emis.de/ft/11086>, proof of Theorem 3.3, p. 262, which starts by choosing "an arbitrary morphism"
  from the curve to the projective line defined over $\overline{\mathbb{Q}}$.
- The Stacks project, Theorem 53.2.6 (Tag 0BY1), <https://stacks.math.columbia.edu/tag/0BY1>, and
  Lemma 53.2.4 (Tag 0CCL), <https://stacks.math.columbia.edu/tag/0CCL>.
