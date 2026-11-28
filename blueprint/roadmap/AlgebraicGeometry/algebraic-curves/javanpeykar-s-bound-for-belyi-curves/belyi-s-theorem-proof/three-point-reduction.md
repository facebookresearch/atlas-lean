# Moving finitely many rational points to $0$, $1$ and $\infty$

Let $T$ be a finite subset of $\mathbb{P}^1(\mathbb{Q}) = \mathbb{Q} \cup \{\infty\}$. Then there
is a rational function $q \in \mathbb{Q}(z)$ with $q(T) \subset \{0, 1, \infty\}$ that is a
composite of fractional linear transformations $z \mapsto \frac{az + b}{cz + d}$ with $a, b, c, d
\in \mathbb{Q}$ and $ad - bc \ne 0$, and of [polynomials](../belyi-polynomial.md) $q_1 =
c_{m,n} \, z^m (1 - z)^n$ with $m, n \ge 1$ and $c_{m,n} = \frac{(m+n)^{m+n}}{m^m n^n}$. It is
built by induction on the number $r$ of elements of $T$:

- if $r \le 3$, $q$ is a fractional linear transformation;
- if $r > 3$, $q = q_2 \circ q_1 \circ \varphi$, where $\varphi$ is a fractional linear
  transformation with $0, 1, \infty \in \varphi(T)$ and a fourth point $\frac{m}{m+n}$ of
  $\varphi(T)$ in the open interval $(0, 1)$, $q_1 = c_{m,n} \, z^m (1 - z)^n$, and $q_2$ is the
  composite given by the induction for the set $q_1(\varphi(T))$, which has fewer than $r$ elements
  and contains $0$, $1$ and $\infty$.

This is the construction of Köck's proof of his Lemma 3.6, which he states over $\mathbb{C}$ (see
Sources).

## Depends on

- [The polynomial $c \, z^m (1 - z)^n$ of Köck's Lemma 3.6](../belyi-polynomial.md), for
  the polynomials $q_1$

## Proof depends on

- [Values and derivative of the polynomial $c \, z^m (1 - z)^n$](../belyi-polynomial-spec.md), for
  $q_1(0) = q_1(1) = 0$ and $q_1(\frac{m}{m+n}) = 1$, so that $q_1$ maps $0$, $\frac{m}{m+n}$, $1$
  and $\infty$ onto $\{0, 1, \infty\}$

The other inputs are listed under Expansion.

## Proof sketch

For three distinct points $a, b, c \in \mathbb{P}^1(\mathbb{Q})$, the fractional linear
transformation $z \mapsto \frac{(z - a)(b - c)}{(z - c)(b - a)}$, read with the usual conventions
when one of them is $\infty$, has rational coefficients and sends $a$, $b$, $c$ to $0$, $1$,
$\infty$; this settles $r \le 3$. For $r > 3$, after such a map, $z \mapsto 1/z$ moves a point
greater than $1$ into $(0, 1)$ and $z \mapsto z/(z - 1)$ moves a negative one there; both have
rational coefficients and permute $\{0, 1, \infty\}$. A rational point of $(0, 1)$ is
$\frac{m}{m+n}$ with $m, n \ge 1$. Then $q_1$ sends $0$ and $1$ to $0$, $\frac{m}{m+n}$ to $1$
and $\infty$ to $\infty$, so $q_1(\varphi(T))$ has fewer elements and contains $0$, $1$, $\infty$.

## Expansion

This node is still to be broken down. A good expansion states and links:

- fractional linear transformations with rational coefficients, acting on
  $\mathbb{P}^1(\mathbb{Q})$, and the one that sends three distinct rational points to $0$, $1$,
  $\infty$, which settles $\lvert T \rvert \le 3$;
- for $\lvert T \rvert > 3$ with $0, 1, \infty \in T$, a fractional linear transformation with
  rational coefficients permuting $\{0, 1, \infty\}$ that moves a fourth point of $T$ into the open
  interval $(0, 1)$, where it is $\frac{m}{m + n}$ with $m, n$ positive integers ($z \mapsto 1/z$
  for a point greater than $1$, $z \mapsto z/(z - 1)$ for a negative point);
- the induction on $\lvert T \rvert$ over $\mathbb{Q}$: $q_1(T)$ has fewer elements than $T$ and
  contains $0$, $1$ and $\infty$, as $q_1$ maps four points of $T$ onto $\{0, 1, \infty\}$.

## Sources

- B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, <https://www.emis.de/ft/11086>, proof of Lemma 3.6, p. 263, whose construction the statement is: "We use
  induction on the number $r$ of elements in $T$. If $r \le 3$, there is a fractional linear
  transformation $q$ with $q(T) \subseteq \{0, 1, \infty\}$. So, let $r > 3$. After composing
  with an appropriate fractional linear transformation, we may assume that $0, 1, \infty \in T$
  and that there is a fourth point in $T$ which lies in the interval between $0$ and $1$, i.e.,
  which is of the form $\frac{m}{m+n}$ where $m, n \in \mathbb{N}$. We now consider the polynomial
  $q_1(z) := \frac{(m+n)^{m+n}}{m^m n^n} z^m (1 - z)^n \in \mathbb{Q}[z]$", and then "the
  induction hypothesis applied to $q_1(T)$" gives $q_2$ and $q := q_2 \circ q_1$.
- Köck's own formulation, over $\mathbb{C}$, is his Lemma 3.6, p. 263: "Let $T$ be a finite subset
  of $\mathbb{Q}$. Then there is a non-constant morphism $q \colon \mathbb{P}^1_{\mathbb{C}} \to
  \mathbb{P}^1_{\mathbb{C}}$ such that $q(T)$ and the critical values of $q$ lie in $\{0, 1,
  \infty\}$". His proof assumes $0, 1, \infty \in T$, and his proof of Theorem 3.3, p. 262, applies
  the lemma to a set containing $\infty$.
