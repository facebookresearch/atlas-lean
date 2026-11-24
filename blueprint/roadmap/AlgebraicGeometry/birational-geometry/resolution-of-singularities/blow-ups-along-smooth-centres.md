# Blow-ups along smooth centres and total transforms

This node is still to be broken down: the statements are precise, but their proofs are not. It
collects the facts about blow-ups and simple normal crossings that Kollár records with his
definitions, and that the [simple normal crossing divisor](../simple-normal-crossing-divisor.md)
page recalls beside them. Let $X$ be a smooth variety of pure dimension $n$ over a perfect field
$k$, with the notation of that page.

1. (Coordinates.) If $z_1, \dots, z_n$ is a regular system of parameters of $\mathcal{O}_{x,X}$ at a
   closed point $x$, the closed subschemes $(z_{j_1} = \dots = z_{j_s} = 0)$ are smooth over $k$
   near $x$. A subvariety $Z$ that has simple normal crossings with an snc divisor $E$ is smooth,
   and if $Z \not\subset E$ then $E|_Z$ is an snc divisor on $Z$. An ideal sheaf on $X$ is locally
   monomial, that is, generated near every point by $\prod_i z_i^{c_i}$ for suitable local
   coordinates $z_i$ and natural numbers $c_i$, if and only if it is the ideal sheaf of an effective
   divisor with snc support (Kollár, 16).
2. (Smooth blow-ups.) If $Z \subset X$ is a smooth closed subvariety, the blow-up $B_Z X$ and its
   exceptional divisor $F = \pi_{Z,X}^{-1}(Z)$ are smooth.
3. (Trivial blow-ups.) If $Z$ is an effective Cartier divisor, $\pi_{Z,X}$ is an isomorphism and $F
   = Z$.
4. (Flat base change.) For a flat morphism $h \colon Y \to X$ and a closed subscheme $Z \subset X$,
   $B_{Z \times_X Y} Y = B_Z X \times_X Y$. Hence, for a smooth $h$, the pull-back $h^* \Pi$ of a
   blow-up sequence $\Pi$ is a blow-up sequence, smooth if $\Pi$ is.
5. (Exceptional sets.) For a birational morphism $g \colon X' \to X$, $\mathrm{Ex}(g)$ is a divisor
   (Kollár, Definition 25, after Shafarevich, II.4.4). For a smooth blow-up sequence $\Pi$ starting
   with $X$ in which no connected component of a centre is a divisor,
   $\mathrm{Ex}_{\mathrm{tot}}(\Pi) = \mathrm{Ex}(\Pi)$.
6. (Total transforms.) If $E$ is an snc divisor on $X$ and the centres of a smooth blow-up sequence
   $\Pi$ have simple normal crossings with $E$, then the total transform
   $\Pi^{-1}_{\mathrm{tot}}(E)$ is an snc divisor.

A good expansion has pages for: the computations in a regular system of parameters behind 1 (Kollár,
16 and Definition 24); the charts $z_j = z_i u_j$ of the blow-up of a coordinate centre, after étale
coordinates, for 2 and 6; the Rees algebra of an ideal sheaf and its compatibility with flat base
change, for 3 and 4; and the purity of the exceptional set of a birational morphism to a smooth
variety, for 5 (Shafarevich, II.4.4).

## Depends on

- [Simple normal crossing divisor](../simple-normal-crossing-divisor.md), for snc divisors,
  blow-ups, blow-up sequences, exceptional sets and total transforms
- [Geometrically reduced variety over a field](../../schemes-and-morphisms/varieties-over-a-field/is-variety.md),
  for the underlying variety over $k$, which the statements take smooth and of pure dimension $n$

## Proof depends on

The steps of its proof are not pages yet: the computations in a regular system of parameters, the
charts of the blow-up of a coordinate centre, the Rees algebra and its compatibility with flat base
change, the blow-up of an effective Cartier divisor, and the purity of the exceptional set
(Shafarevich, II.4.4).

## Sources

- J. Kollár, "Resolution of singularities – Seattle lecture", arXiv:math/0508332 (version 3),
  <https://arxiv.org/abs/math/0508332v3>, §3: 16 (monomial ideal sheaves, p. 16), Notation 19 and
  Warning 20 (blow-ups, trivial and empty blow-ups, p. 17), Definition 24 (simple normal crossing
  divisors, p. 18), Definition 25 (exceptional sets, total exceptional set and total transform, pp.
  18–19) and 30.1 (pull-back by smooth morphisms, p. 21).
- I. R. Shafarevich, *Basic Algebraic Geometry 1*, second edition, Springer, 1994: II.4.4 (the
  exceptional set of a birational morphism to a smooth variety), as cited in Kollár's Definition 25.
