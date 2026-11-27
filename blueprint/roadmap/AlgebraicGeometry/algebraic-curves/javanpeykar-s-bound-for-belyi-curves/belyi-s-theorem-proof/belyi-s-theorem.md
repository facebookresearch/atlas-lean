# Belyi's theorem

Let $K$ be a number field and $C$ a curve over $K$, that is, a $K$-scheme that is proper, smooth
of relative dimension $1$ and geometrically irreducible, and let $C_{\bar K}$ be its
[base change to an algebraic closure](../over-algebraic-closure.md) $\bar K$ of $K$. Then
$C_{\bar K}$ has a [Belyi map of some degree](../has-belyi-map-of-degree.md): a finite morphism
$C_{\bar K} \to \mathbb{P}^1_{\bar K}$ that is unramified over $\mathbb{P}^1_{\bar K} \setminus
\{0, 1, \infty\}$ and has constant degree $d$ for some $d$.

Belyi's theorem, as Javanpeykar states it, gives for every smooth projective connected curve $X$
over $\overline{\mathbb{Q}}$ a finite morphism $X \to \mathbb{P}^1_{\overline{\mathbb{Q}}}$
ramified over at most three points; every such curve is $C_{\bar K}$ for a curve $C$ over a number
field $K$, and an automorphism of $\mathbb{P}^1_{\bar K}$ that maps the branch points into
$\{0, 1, \infty\}$ turns that morphism into a Belyi map of the same degree. So the
[Belyi degree](../belyi-degree.md) $\deg_B(X)$ is the least degree of a Belyi map of $X$.

The proof follows Köck's proof of the "only if" direction of his Theorem 3.3. Choose a finite
morphism $t' \colon C_{\bar K} \to \mathbb{P}^1_{\bar K}$; it is unramified outside a finite set
$S$ of closed points, that is, of elements of $\bar K \cup \{\infty\}$. As $\bar K$ is an algebraic
closure of $\mathbb{Q}$, there is a nonconstant $p \in \mathbb{Q}[z]$ with $p(S \setminus
\{\infty\}) \subset \mathbb{Q}$ and $p(r) \in \mathbb{Q}$ at the zeros $r$ of $p'$; the morphism
$p \circ t'$ is then unramified outside the finite set $T = p(S) \cup \{p(r) : p'(r) = 0\} \cup
\{\infty\} \subset \mathbb{P}^1(\mathbb{Q})$. A finite $q \colon \mathbb{P}^1_{\bar K} \to
\mathbb{P}^1_{\bar K}$ with $q(T) \subset \{0, 1, \infty\}$, unramified outside $\{0, 1,
\infty\}$, makes $t = q \circ p \circ t'$ unramified outside $\{0, 1, \infty\}$. It is finite, as
a composite of finite morphisms, and has constant degree.

## Depends on

- [Base change to an algebraic closure](../over-algebraic-closure.md)
- [Belyi map of a given degree](../has-belyi-map-of-degree.md)

## Proof depends on

- [A curve has a finite morphism to the projective line](finite-morphism-to-the-projective-line.md),
  for $t'$, applied to $C_{\bar K}$
- [Finitely many branch points in characteristic zero](branch-points-of-a-finite-morphism-of-curves.md),
  for the finite set $S$
- [Polynomial with rational critical values](polynomial-with-rational-critical-values.md),
  for $p$
- [Branch points of a polynomial map of the projective line](branch-points-of-a-polynomial-map.md),
  for the branch points of $p$ and $p(\infty) = \infty$
- [Moving finitely many rational points to $0$, $1$ and $\infty$](three-point-reduction.md),
  for $q$
- [Branch locus of a composite](branch-locus-of-a-composite.md), for $p \circ t'$
  and $q \circ p \circ t'$
- [A finite morphism of curves has constant degree](degree-of-a-finite-morphism-of-curves.md),
  for the degree $d$ of $t$

## Sources

- A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, <https://doi.org/10.2140/ant.2014.8.89>, §1.1, p. 89 (statement of Belyi's theorem and definition of the Belyi degree).
- B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, <https://www.emis.de/ft/11086>, Theorem 3.3 and its proof, p. 262, with Lemmas 3.5 and 3.6, pp. 262–263. Köck
  works with complex curves defined over $\overline{\mathbb{Q}}$ and their critical values; his
  Lemma 3.4, that these are $\overline{\mathbb{Q}}$-rational, is not needed over $\bar K$, where
  closed points are rational.
- G. V. Belyi, *On Galois extensions of a maximal cyclotomic field*, Izv. Akad. Nauk SSSR Ser.
  Mat. 43 (1979), 267–276 (in Russian; translated in Math. USSR Izv. 14 (1980), 247–256), as cited
  by Javanpeykar, §1.1, p. 89, and by Köck, p. 253 (not read here).
