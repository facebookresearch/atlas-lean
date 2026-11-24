# Simple normal crossing divisor

Let $X$ be a smooth variety of pure dimension $n$ over a perfect field $k$, for instance a field of
characteristic zero, and $E = \sum_i E_i$ a reduced divisor on $X$ whose components $E_i$ are
smooth. Then $E$ is a *simple normal crossing (snc) divisor* if for every closed point $x \in X$ one
can choose local coordinates $z_1, \dots, z_n$, a regular system of parameters of the local ring
$\mathcal{O}_{x,X}$, such that, for each $i$, either $x \notin E_i$, or $E_i = (z_{c(i)} = 0)$ in a
neighbourhood of $x$ for some index $c(i)$, with $c(i) \ne c(i')$ for $i \ne i'$. The condition is
imposed at closed points, where the local ring has dimension $n$; at the generic point of $X$, for
instance, it has dimension $0$. On a smooth variety whose connected components have different
dimensions, the definition is applied to each component. Over a perfect field the strata cut out by
such parameters are smooth over $k$ (item 1 of
[Blow-ups along smooth centres and total transforms](resolution-of-singularities/blow-ups-along-smooth-centres.md));
over an imperfect field a regular system of parameters is not a system of smooth coordinates: for $k
= \mathbb{F}_p(t)$ and $X = \mathbb{A}^1_k$, $x^p - t$ is a uniformizer at its closed point, which
is not smooth over $k$, and in $\mathbb{A}^2_k$ the curves $y = 0$ and $y = x^p - t$ meet in that
point, with $y$ and $y - x^p + t$ a regular system of parameters there, although they become tangent
over an algebraic closure. Over an arbitrary field one uses instead the geometric condition that the
base change of $E$ to an algebraic closure of $k$ be an snc divisor, keeping the requirement that
the members $E_i$ be smooth over $k$, which that condition does not imply: $V(x^2 + y^2) \subset
\mathbb{A}^2_{\mathbb{R}}$ becomes the two lines $x = \pm iy$ over $\mathbb{C}$, but its single real
component is singular; a subvariety $Z$ is then tested together with $E$ after the same base change.
A subvariety $Z \subset X$ *has simple normal crossings with* $E$ if at every closed point $x \in Z$
the coordinates can be chosen so that in addition $Z = (z_{j_1} = \dots = z_{j_s} = 0)$ near $x$ for
some indices $j_1, \dots, j_s$. Some of the $E_i$ may contain such a $Z$; for the smoothness of $Z$,
and for $E|_Z$ being an snc divisor on $Z$ when no irreducible component of $Z$ is contained in $E$,
see item 1 of the same page. An effective divisor $\sum_i c_i E_i$ with integers $c_i \ge 1$ whose
reduced divisor $\sum_i E_i$ is an snc divisor has *snc support*; Kollár also calls it a simple
normal crossing divisor. Its ideal sheaf is generated near every closed point $x$, in the
coordinates above, by $\prod_{i \colon x \in E_i} z_{c(i)}^{c_i}$ up to a unit, so it is locally
monomial in Kollár's sense (16); for the converse, that every locally monomial ideal sheaf is of
this form, see item 1 of the same page.

**$\mathbb{Q}$-divisors.** A $\mathbb{Q}$-divisor on $X$ is a finite sum $D = \sum_i a_i D_i$ of
distinct prime divisors $D_i$ with coefficients $a_i \in \mathbb{Q}$; it is effective if all $a_i
\ge 0$. Its round-down, or integral part, is $\lfloor D \rfloor = \sum_i \lfloor a_i \rfloor D_i$,
where $\lfloor a \rfloor$ is the integer with $\lfloor a \rfloor \le a < \lfloor a \rfloor + 1$. The
divisor $D$ has *snc support* if the reduced divisor $\sum_{a_i \ne 0} D_i$ is an snc divisor.
Esnault and Viehweg call a reduced divisor whose components are non-singular and intersect each
other transversally a normal crossing divisor, and call $D$ a normal crossing divisor when its
reduced divisor is one.

**Blow-ups.** For a closed subscheme $Z$ of a scheme $X$, $\pi_{Z,X} \colon B_Z X \to X$ is the
blow-up of $Z$ in $X$ and $F = \pi_{Z,X}^{-1}(Z)$ its exceptional divisor. It is a *smooth blow-up*
if $X$ and $Z$ are smooth; for the smoothness of $B_Z X$ and $F$ over $k$, the morphism $\pi_{Z,X}$
itself not being smooth in general, see item 2 of
[Blow-ups along smooth centres and total transforms](resolution-of-singularities/blow-ups-along-smooth-centres.md).
It is *trivial* if $Z$ is a Cartier divisor, and *empty* if $Z = \emptyset$; a trivial blow-up is an
isomorphism with $F = Z$ (see item 3 of the same page). A *blow-up sequence* of length $r$ starting
with $X$ is a chain of blow-ups

$$\Pi \colon X_r \xrightarrow{\ \pi_{r-1}\ } X_{r-1} \to \dots \to X_1 \xrightarrow{\ \pi_0\ } X_0 = X, \qquad \pi_i = \pi_{Z_i, X_i},$$

with specified centres $Z_i \subset X_i$, trivial and empty blow-ups being allowed; it is a *smooth
blow-up sequence* if every $\pi_i$ is a smooth blow-up. For a smooth morphism $h \colon Y \to X$,
the pull-back $h^* \Pi$ is the sequence of the schemes $X_i \times_X Y$ with centres $Z_i \times_X
Y$, again a blow-up sequence, blowing up commuting with flat base change (see item 4 of the same
page).

For a birational morphism $g \colon X' \to X$, the exceptional set $\mathrm{Ex}(g)$ is the set of
points of $X'$ at which $g$ is not a local isomorphism; for a birational morphism of varieties with
$X$ smooth it is empty or of pure codimension one (see item 5 of
[Blow-ups along smooth centres and total transforms](resolution-of-singularities/blow-ups-along-smooth-centres.md)).
For a smooth blow-up sequence $\Pi$ starting with a smooth variety $X$, the total exceptional set is

$$\mathrm{Ex}_{\mathrm{tot}}(\Pi) = \bigcup_{i=0}^{r-1} (\pi_i \circ \dots \circ \pi_{r-1})^{-1}(Z_i),$$

which equals $\mathrm{Ex}(\Pi)$ when every connected component of every centre has codimension at
least $2$ (see item 5 of the same page). It is not enough that no blow-up be trivial: in
$\mathbb{A}^2$, blowing up the disjoint union of a line and a point off it is not trivial,
$\mathrm{Ex}$ is the exceptional curve over the point, and $\mathrm{Ex}_{\mathrm{tot}}$ also
contains the inverse image of the line. If $E$ is an snc divisor on $X$, the centres of $\Pi$ *have
simple normal crossings with* $E$ if each $Z_i$ has simple normal crossings with $(\pi_0 \circ \dots
\circ \pi_{i-1})^{-1}_*(E) + \mathrm{Ex}_{\mathrm{tot}}(\pi_0 \circ \dots \circ \pi_{i-1})$, where
$(\,\cdot\,)^{-1}_*$ denotes the birational transform. The *total transform* of $E$ is the reduced
divisor $\Pi^{-1}_{\mathrm{tot}}(E) = \Pi^{-1}_*(E) + \mathrm{Ex}_{\mathrm{tot}}(\Pi)$, not the
pull-back of $E$ with multiplicities; for its being an snc divisor when the centres have simple
normal crossings with $E$, see item 6 of the same page.

**Blow-up sequence functors.** For a morphism $h \colon Y \to X$ and an ideal sheaf $I \subset
\mathcal{O}_X$, $h^* I = h^{-1} I \cdot \mathcal{O}_Y$ denotes the inverse image ideal sheaf. A
*blow-up sequence functor* $B$ assigns to every triple $(X, I, E)$ of its domain, made of a scheme
$X$, an ideal sheaf $I \subset \mathcal{O}_X$ that is nonzero on every irreducible component of $X$
and a divisor $E$ on $X$ (whose components Kollár takes with an ordered index set), a blow-up
sequence $B(X, I, E)$ starting with $X$, with specified centres; its length, the schemes $X_i$ and
the centres $Z_i$ depend on $(X, I, E)$. It *commutes with smooth morphisms* if $B(Y, h^* I,
h^{-1}(E)) = h^* B(X, I, E)$ for every smooth surjective morphism $h \colon Y \to X$, and if for
every smooth morphism $h$ the sequence $B(Y, h^* I, h^{-1}(E))$ is obtained from $h^* B(X, I, E)$ by
deleting the blow-ups with empty centre and renumbering. It *commutes with change of fields* if, for
$X$ of finite type over a field $K$ and every field extension $\sigma \colon K \hookrightarrow L$,
the sequence attached to the base change $(X_{L,\sigma}, I_{L,\sigma}, E_{L,\sigma})$, where
$X_{L,\sigma} = X \times_{\operatorname{Spec} K} \operatorname{Spec} L$, is the base change of $B(X,
I, E)$.

## Depends on

- [Geometrically reduced variety over a field](../schemes-and-morphisms/varieties-over-a-field/is-variety.md),
  for the underlying variety over $k$, which the definition takes smooth and of pure dimension $n$

## Proof depends on

This node has no prerequisites.

Its statements are definitions. The facts about blow-ups recalled beside them, with the references
above, are the targets of the node on blow-ups along smooth centres, which depends on this page.

## Sources

- J. Kollár, "Resolution of singularities – Seattle lecture", arXiv:math/0508332 (version 3),
  <https://arxiv.org/abs/math/0508332v3>, §3: Notation 15 (inverse image ideal sheaves, p. 15), 16
  (monomial ideal sheaves, p. 16), Notation 19 and Warning 20 (blow-ups, trivial and empty blow-ups,
  p. 17), Definition 24 (simple normal crossing divisors and subvarieties having simple normal
  crossings with them, p. 18), Definition 25 (exceptional sets, total exceptional set, centres
  having simple normal crossings with $E$, total transform, pp. 18–19), Definition 29 (blow-up
  sequences, p. 21), 30.1 (pull-back by smooth morphisms, p. 21), Definition 31 (blow-up sequence
  functors, p. 22), 34.1 and 34.2 (commuting with smooth morphisms and with change of fields, pp.
  23–24). Sections 1–13 of the lecture are Sections 3.1–3.13 of the chapter "Strong resolution in
  characteristic zero" of J. Kollár, *Lectures on Resolution of Singularities*, Annals of
  Mathematics Studies 166, Princeton University Press, 2007.
- R. Lazarsfeld, "A short course on multiplier ideals", arXiv:0901.0651 (version 1),
  <https://arxiv.org/abs/0901.0651v1>, pp. 2–3: effective $\mathbb{Q}$-divisors, Exercise 1.2
  (divisors with simple normal crossing support) and the round-down $[D]$ used in Exercise 1.2 and
  Definition 1.3.
- H. Esnault and E. Viehweg, *Lectures on Vanishing Theorems*, DMV Seminar 20, Birkhäuser, 1992;
  electronic version on H. Esnault's page, <https://page.mi.fu-berlin.de/esnault/books/esvibuch.pdf>
  (page numbers of the electronic version): the opening of Lecture 2 (reduced normal crossing
  divisors, p. 11), Notation 3.1 b) and d) (integral part of a $\mathbb{Q}$-divisor, normal crossing
  divisors with multiplicities, p. 19) and Remark 3.4 a) (p. 21).
