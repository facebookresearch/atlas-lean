# Cohomological dimension two but geometric dimension three

Take the presentation two-complex with generators $x,y$ and relators $x^2y^{-5}$ and $x^2(yx^{-1})^3$. Subdivide each generator loop into three edges, and fan each relator polygon from its own center, keeping distinct radial edges and sectors and gluing the boundary by the signed word. Let $\Gamma$ be the comparability graph on the cells (adjacency by proper face incidence). The graph has one vertex for each of the seven 0-cells, 51 edges, and 45 sectors of the subdivided complex. Take the right-angled Artin group on $\Gamma$ and its height homomorphism to $\mathbb Z$ sending every generator to $1$. Its kernel $G$ is finitely generated and residually finite.

The projective dimension of the trivial left $\mathbb Z[G]$-module $\mathbb Z$ is two. There is a path-connected Hausdorff CW complex with no cells above dimension three, fundamental group $G$, and a surjective covering map from a contractible space. There is no such complex with no cells above dimension two, with no cardinality restriction on the cells of the excluded complex.

## Depends on

- [Artin group presentation](../presentations-and-decision-problems/braid-and-artin/artin-groups/artin-group.md)
- Subdivided presentation complex and face graph; Artin height map; integral group-ring projective dimension and ordinary classifying CW spaces.

## Proof depends on

- Control finiteness properties of the specific kernel and establish nonexistence of a two-dimensional classifying CW model, not just the lack of one among finite complexes.

## Expansion

Match the literal signed-word incidence graph to a CW model, check the height map on commuting relators, then separate residual finiteness/cohomological dimension from the geometric-dimension obstruction.

## Sources

- OpenAI Math, [`source_main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EilenbergGanea.lean#L113-L119) (statement and local definitions).
