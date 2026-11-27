# Falconer's distance set theorem

For every integer $d \ge 2$ and every compact set $E \subseteq \mathbb{R}^d$ whose Hausdorff dimension
is strictly greater than $(d + 1)/2$, the distance set $\{|x - y| : x, y \in E\}$ has positive
one-dimensional Lebesgue measure.

## Idea

This is the result that opened the problem in 1985. Given $E$ with $\dim_H E > (d + 1)/2$, choose
$t$ with $(d + 1)/2 < t < \dim_H E$; by Frostman's lemma $E$ carries a probability measure $\mu$
with finite $t$-energy. Falconer showed that for $t > (d + 1)/2$ the pushforward of
$\mu \otimes \mu$ under $(x, y) \mapsto |x - y|$, a measure on the distance set, then has a
square-integrable density, using the decay of the Fourier transform of surface measure on spheres;
a measure with such a density forces its support to have positive length. In the plane the theorem
says that the planar threshold is at most $3/2$.

## Statements

- [Falconer's distance set theorem](falconer1985-general-sufficiency-holds.md)
- [Statement of Falconer's distance set theorem](falconer1985-general-sufficiency.md): the statement as a proposition.
- [Falconer's upper bound for the planar distance threshold](upper-bound-falconer1985-holds.md): the planar case, the threshold is at most $3/2$.
- [Statement of the upper bound $3/2$ for the planar distance threshold](upper-bound-falconer1985.md): that bound as a proposition.

## Background

- [Distance set](../distance-sets/README.md)
- [Planar Falconer distance threshold](../planar-falconer-threshold/README.md)

## Sources

- L. Guth, A. Iosevich, Y. Ou and H. Wang, arXiv:1808.09346v1, introduction, reporting Falconer (1985).
