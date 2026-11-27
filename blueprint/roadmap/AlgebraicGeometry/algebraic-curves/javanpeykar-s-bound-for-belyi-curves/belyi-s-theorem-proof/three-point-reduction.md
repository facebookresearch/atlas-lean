# Moving finitely many rational points to $0$, $1$ and $\infty$

Let $k$ be an algebraically closed field of characteristic $0$ and $T$ a finite subset of
$\mathbb{P}^1(\mathbb{Q}) = \mathbb{Q} \cup \{\infty\} \subset \mathbb{P}^1(k)$. Then there is a
finite morphism $q \colon \mathbb{P}^1_k \to \mathbb{P}^1_k$ with $q(T) \subset \{0, 1, \infty\}$
that is unramified over $\mathbb{P}^1_k \setminus \{0, 1, \infty\}$.

Köck states this over $\mathbb{C}$, for a finite subset $T$ of $\mathbb{Q}$, and applies it to a
set that may contain $\infty$; his proof moves $\infty$ like any other point and uses only
fractional linear transformations defined over $\mathbb{Q}$ and the polynomials $c \, z^m
(1 - z)^n$, so it applies over $k$ to subsets of $\mathbb{P}^1(\mathbb{Q})$.

## Depends on

None among the pages.

## Proof depends on

- [Values and derivative of the polynomial $c \, z^m (1 - z)^n$](belyi-polynomial.md), for the
  polynomial $q_1$ that maps $0$, $\frac{m}{m + n}$, $1$ and $\infty$ into $\{0, 1, \infty\}$
- [Branch points of a polynomial map of the projective line](branch-points-of-a-polynomial-map.md),
  so that $q_1$ is unramified over $\mathbb{P}^1_k \setminus \{0, 1, \infty\}$
- [Branch locus of a composite](branch-locus-of-a-composite.md), for $q = q_2 \circ q_1$

The other inputs are listed under Expansion.

## Expansion

This node is still to be broken down. A good expansion states and links:

- fractional linear transformations with rational coefficients as automorphisms of
  $\mathbb{P}^1_k$, unramified everywhere, and their transitivity on triples of distinct points of
  $\mathbb{P}^1(\mathbb{Q})$, which settles $\lvert T \rvert \le 3$;
- for $\lvert T \rvert > 3$ with $0, 1, \infty \in T$, a fractional linear transformation
  permuting $\{0, 1, \infty\}$ that moves a fourth point of $T$ into the open interval $(0, 1)$,
  where it is $\frac{m}{m + n}$ with $m, n$ positive integers ($z \mapsto 1/z$ for a point greater
  than $1$, $z \mapsto z/(z - 1)$ for a negative point);
- the induction on $\lvert T \rvert$: $q_1(T) \subset \mathbb{P}^1(\mathbb{Q})$ has fewer elements
  than $T$, as $q_1$ maps four points of $T$ into $\{0, 1, \infty\}$, and composites of finite
  morphisms are finite.

## Sources

- B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, <https://www.emis.de/ft/11086>, Lemma 3.6 and its proof, p. 263, and its use in the proof of Theorem 3.3, p. 262.
