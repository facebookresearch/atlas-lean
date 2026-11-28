# Moving finitely many rational points to $0$, $1$ and $\infty$

Let $T$ be a finite subset of $\mathbb{P}^1(\mathbb{Q}) = \mathbb{Q} \cup \{\infty\} \subset
\mathbb{P}^1(\mathbb{C})$. Then there is a [Belyi map](../is-belyi-map.md) $q \colon
\mathbb{P}^1_{\mathbb{C}} \to \mathbb{P}^1_{\mathbb{C}}$ over $\mathbb{C}$ with $q(T) \subset
\{0, 1, \infty\}$: a finite morphism whose critical values lie in $\{0, 1, \infty\}$, so that it
is unramified over the [complement of $0$, $1$ and $\infty$](../belyi-locus.md).

This is Köck's Lemma 3.6. He states it for a finite subset $T$ of $\mathbb{Q}$; his proof assumes
$0, 1, \infty \in T$, and his proof of Theorem 3.3 applies it to a set containing $\infty$.

Köck's proof builds $q$ by induction on the number $r$ of elements of $T$ from fractional linear
transformations and the polynomials $c \, z^m (1 - z)^n$: "If $r \le 3$, there is a fractional
linear transformation $q$ with $q(T) \subseteq \{0, 1, \infty\}$. So, let $r > 3$. After composing
with an appropriate fractional linear transformation, we may assume that $0, 1, \infty \in T$ and
that there is a fourth point in $T$ which lies in the interval between $0$ and $1$, i.e., which is
of the form $\frac{m}{m+n}$ where $m, n \in \mathbb{N}$. We now consider the polynomial
$q_1(z) := \frac{(m+n)^{m+n}}{m^m n^n} z^m (1 - z)^n \in \mathbb{Q}[z]$", and then $q = q_2 \circ
q_1$ with $q_2$ given by the induction applied to $q_1(T)$. So every map of the construction is
defined over $\mathbb{Q}$: the polynomials $q_1$ are in $\mathbb{Q}[z]$, and the fractional linear
transformations move points of $\mathbb{P}^1(\mathbb{Q})$ to $0$, $1$, $\infty$ and
$\frac{m}{m+n}$.

## Depends on

- [Belyi map](../is-belyi-map.md), for the property of $q$
- [The complement of $0$, $1$ and $\infty$ in the projective line](../belyi-locus.md), the open
  subscheme over which $q$ is unramified

## Proof depends on

- [Values and derivative of the polynomial $c \, z^m (1 - z)^n$](belyi-polynomial.md), for the
  polynomial $q_1$ that maps $0$, $\frac{m}{m + n}$, $1$ and $\infty$ into $\{0, 1, \infty\}$
- [Branch points of a polynomial map of the projective line](branch-points-of-a-polynomial-map.md),
  so that $q_1$ is unramified over $\mathbb{P}^1_{\mathbb{C}} \setminus \{0, 1, \infty\}$
- [Branch locus of a composite](../../../schemes-and-morphisms/branch-locus-of-a-composite.md), for $q = q_2 \circ q_1$

The other inputs are listed under Expansion.

## Expansion

This node is still to be broken down. A good expansion states and links:

- fractional linear transformations as automorphisms of $\mathbb{P}^1_{\mathbb{C}}$, unramified
  everywhere, and their transitivity on triples of distinct points of
  $\mathbb{P}^1(\mathbb{Q})$, which settles $\lvert T \rvert \le 3$;
- for $\lvert T \rvert > 3$ with $0, 1, \infty \in T$, a fractional linear transformation
  permuting $\{0, 1, \infty\}$ that moves a fourth point of $T$ into the open interval $(0, 1)$,
  where it is $\frac{m}{m + n}$ with $m, n$ positive integers ($z \mapsto 1/z$ for a point greater
  than $1$, $z \mapsto z/(z - 1)$ for a negative point);
- the induction on $\lvert T \rvert$: $q_1(T) \subset \mathbb{P}^1(\mathbb{Q})$ has fewer elements
  than $T$, as $q_1$ maps four points of $T$ into $\{0, 1, \infty\}$, and composites of finite
  morphisms are finite.

## Sources

- B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, <https://www.emis.de/ft/11086>, Lemma 3.6 and its proof, p. 263: "Let $T$ be a finite subset of $\mathbb{Q}$. Then there is a
  non-constant morphism $q \colon \mathbb{P}^1_{\mathbb{C}} \to \mathbb{P}^1_{\mathbb{C}}$ such
  that $q(T)$ and the critical values of $q$ lie in $\{0, 1, \infty\}$"; and its use in the proof
  of Theorem 3.3, p. 262.
