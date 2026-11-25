# Integration over quotients of locally compact groups

This node is still to be broken down. It covers the invariant measures on quotients of locally compact
groups and the integration formula relating them to Haar measures, which the pages on discrete series
and on automorphic forms use. Let $G$ be a locally compact Hausdorff group with a countable basis of open
sets, as are the Lie groups and the groups of adelic points that use this node, with a left Haar measure
$dg$, and $H$ a closed subgroup with a left Haar measure $dh$. The theorems below hold without the countable
basis, but the source below assumes it; the general case needs a source of its own.

- **Weil's formula.** There is a nonzero $G$-invariant Radon measure $d\dot g$ on $G/H$ if and only if the
  modular functions of $G$ and $H$ agree on $H$ (for instance if both are unimodular); it is then unique up to a
  positive scalar, and it can be normalized so that
  $\int_G f(g)\, dg = \int_{G/H} \int_H f(gh) \, dh \, d\dot g$ for every $f \in C_c(G)$, and then for every
  integrable $f$. For closed subgroups $H_1 \subseteq H_2$ of a unimodular $G$, all unimodular, with compatibly
  normalized invariant measures, integration over $G/H_1$ is the iterated integration over $G/H_2$ and $H_2/H_1$,
  $\int_{G/H_1} f = \int_{G/H_2} \int_{H_2/H_1} f(g h) \, d\dot h \, d\dot g$, rather than a product of arbitrary measures.
- **Compact normal subgroups.** If $H$ is compact and normal and $dh$ has total mass $1$, the image of
  $dg$ under $G \to G/H$ is a Haar measure on the locally compact group $G/H$, and
  $\int_G f(g)\, dg = \int_{G/H} f(gH) \, d(gH)$ for every integrable function $f$ invariant under $H$; in
  particular this holds for a compact centre $Z$ and the function $\lvert \langle \pi(g)v, w \rangle \rvert^2$
  of a representation with a unitary central character. For a noncompact centre, square-integrability
  over $G/Z$ is not square-integrability over $G$.

## Expansion

A good expansion has a page for the existence and uniqueness of the invariant measure on $G/H$ with
Weil's formula, and one for the case of a compact normal subgroup, each citing a pinned source with
locators.

It also writes out these steps of its own proof:

- the averaging map $C_c(G) \to C_c(G/H)$, $f \mapsto \int_H f(\cdot\, h) \, dh$, being onto, for Weil's formula.

## Depends on

- [Haar measure](is-haar-measure.md), for Haar measures
- [Modular function of a locally compact group](modular-character.md), for the modular function
- [Regular measure](../measures/regular-measures/radon-measures/regular.md), for Radon measures, the regular measures, for both items

## Proof depends on

- [Existence of Haar measure](existence-and-uniqueness-of-haar-measure/is-haar-measure-haar-measure.md), for the existence of Haar measure, for Weil's formula
- [Uniqueness of regular left-invariant measures up to a scalar](existence-and-uniqueness-of-haar-measure/is-mul-left-invariant-eq-smul-of-regular.md), for the uniqueness of Haar measure up to a scalar, for Weil's formula

## Sources

- P. Garrett, "Unitary representations of topological groups", notes, 3 August 2014,
  <https://www-users.cse.umn.edu/~garrett/m/repns/notes_2014-15/06a_unitary_of_top.pdf>: §4, Lemma [4.0.5],
  p. 7 (the averaging maps are onto) and Theorem [4.0.6], p. 8 ($H \backslash G$ has a right $G$-invariant measure if
  and only if $\Delta_G|_H = \Delta_H$, unique up to scalars, with the integration formula), for locally compact
  Hausdorff countably based groups, with right Haar measures and right cosets ($G/H$ by inversion); this is
  the generality stated above.
- J. Arthur, "An introduction to the trace formula", in *Harmonic Analysis, the Trace Formula, and
  Shimura Varieties*, Clay Math. Proc. 4, American Mathematical Society, 2005, 1–263,
  <https://www.claymath.org/library/proceedings/cmip04c.pdf>: §1, p. 9 ("for any sequence
  $H_1 \subset H_2 \subset H$ of unimodular groups, a right invariant measure on $H_1 \backslash H$ can be
  written as the product of right invariant measures on $H_2 \backslash H$ and $H_1 \backslash H_2$
  respectively"), the chain rule for unimodular groups.
- J. Bernstein and B. Krötz, "Smooth Fréchet globalizations of Harish-Chandra modules", Israel J.
  Math. 199 (2014), 45–111, arXiv:0812.1684 (version 3): §10.2, equation (10.1) (square-integrability
  and the formal degree over $G/Z$ for the quotient measure).
