# Integration over quotients of locally compact groups

This node is still to be broken down. It covers the invariant measures on quotients of locally compact
groups and the integration formula relating them to Haar measures, which the pages on discrete series
and on automorphic forms use. Let $G$ be a locally compact group with a left Haar measure $dg$ and $H$
a closed subgroup with a left Haar measure $dh$.

- **Weil's formula.** If the modular functions of $G$ and $H$ agree on $H$ (for instance if both are
  unimodular), there is a nonzero $G$-invariant Radon measure $d\dot g$ on $G/H$, unique up to a positive
  scalar, and it can be normalized so that
  $\int_G f(g)\, dg = \int_{G/H} \int_H f(gh) \, dh \, d\dot g$ for every $f \in C_c(G)$, and then for every
  integrable $f$. For a chain $H_1 \subseteq H_2 \subseteq G$ of unimodular groups the invariant measure on
  $G/H_1$ is the product of those on $G/H_2$ and $H_2/H_1$.
- **Compact normal subgroups.** If $H$ is compact and normal and $dh$ has total mass $1$, the image of
  $dg$ under $G \to G/H$ is a Haar measure on the locally compact group $G/H$, and
  $\int_G f(g)\, dg = \int_{G/H} f(gH) \, d(gH)$ for every integrable function $f$ invariant under $H$; in
  particular this holds for a compact centre $Z$ and the function $\lvert \langle \pi(g)v, w \rangle \rvert^2$
  of a representation with a unitary central character. For a noncompact centre, square-integrability
  over $G/Z$ is not square-integrability over $G$.

A good expansion has a page for the existence and uniqueness of the invariant measure on $G/H$ with
Weil's formula, and one for the case of a compact normal subgroup, each citing a pinned source with
locators.

## Depends on

- Not yet a page: Radon measures on locally compact spaces, Haar measures and modular functions, for both items

## Proof depends on

- Not yet a page: the existence and uniqueness of Haar measure, and the averaging map $C_c(G) \to C_c(G/H)$, $f \mapsto \int_H f(\cdot\, h) \, dh$, being onto, for Weil's formula

## Sources

- J. Arthur, "An introduction to the trace formula", in *Harmonic Analysis, the Trace Formula, and
  Shimura Varieties*, Clay Math. Proc. 4, American Mathematical Society, 2005, 1–263,
  <https://www.claymath.org/library/proceedings/cmip04c.pdf>: §1, p. 9 ("for any sequence
  $H_1 \subset H_2 \subset H$ of unimodular groups, a right invariant measure on $H_1 \backslash H$ can be
  written as the product of right invariant measures on $H_2 \backslash H$ and $H_1 \backslash H_2$
  respectively").
- J. Bernstein and B. Krötz, "Smooth Fréchet globalizations of Harish-Chandra modules", Israel J.
  Math. 199 (2014), 45–111, arXiv:0812.1684 (version 3): §10.2, equation (10.1) (square-integrability
  and the formal degree over $G/Z$ for the quotient measure).
