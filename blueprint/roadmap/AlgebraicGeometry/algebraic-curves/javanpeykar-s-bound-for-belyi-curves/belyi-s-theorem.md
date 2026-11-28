# Belyi's theorem

This node is still to be broken down. Let $K$ be a number field and $C$ a curve over $K$, that is,
a $K$-scheme that is proper, smooth of relative dimension $1$ and geometrically irreducible, and
let $C_{\bar K}$ be its [base change to an algebraic closure](over-algebraic-closure.md) $\bar K$
of $K$. Then $C_{\bar K}$ has a [Belyi map of some degree](has-belyi-map-of-degree.md): a finite
morphism $C_{\bar K} \to \mathbb{P}^1_{\bar K}$ that is unramified over $\mathbb{P}^1_{\bar K}
\setminus \{0, 1, \infty\}$ and has constant degree $d$ for some $d$.

Belyi's theorem, as Javanpeykar states it, gives for every smooth projective connected curve $X$
over $\overline{\mathbb{Q}}$ a finite morphism $X \to \mathbb{P}^1_{\overline{\mathbb{Q}}}$
ramified over at most three points; every such curve is $C_{\bar K}$ for a curve $C$ over a number
field $K$, and an automorphism of $\mathbb{P}^1_{\bar K}$ that maps the branch points into
$\{0, 1, \infty\}$ turns that morphism into a Belyi map of the same degree. So the
[Belyi degree](belyi-degree.md) $\deg_B(X)$ is the least degree of a Belyi map of $X$.

## Depends on

- [Base change to an algebraic closure](over-algebraic-closure.md)
- [Belyi map of a given degree](has-belyi-map-of-degree.md)

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

Belyi's paper was not read here. A good expansion follows it, with pages for: a finite morphism
$C \to \mathbb{P}^1$ over a number field; the reduction, by composing with polynomial maps defined
over $\mathbb{Q}$, to a morphism whose branch points are rational; the further composition with a
map $x \mapsto c \, x^m (1 - x)^n$ that sends the rational branch points into $\{0, 1, \infty\}$;
the descent from a curve over $\overline{\mathbb{Q}}$ to a number field; and the Möbius
normalization of the branch locus with the constancy of the degree over $\mathbb{P}^1_{\bar K}$.

## Sources

- A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, <https://doi.org/10.2140/ant.2014.8.89>, §1.1, p. 89 (statement of Belyi's theorem and definition of the Belyi degree).
- G. V. Belyi, *On Galois extensions of a maximal cyclotomic field*, Izv. Akad. Nauk SSSR Ser.
  Mat. 43 (1979), 267–276 (in Russian; translated in Math. USSR Izv. 14 (1980), 247–256), as cited
  by Javanpeykar, §1.1, p. 89 (not read here).
