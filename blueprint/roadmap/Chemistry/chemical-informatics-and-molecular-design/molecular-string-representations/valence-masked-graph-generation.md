# Valence masking in sequential graph generation

A generator that builds a molecular graph edge by edge restricts each step by a mask: an edge or a bond order whose indicator is zero is never sampled. The published label mask does not bound the order, and this page states the two-sided restriction that does, as an original correction rather than a reading of the source.

Let a sequential generator hold, at step $t$, a partial graph on typed nodes, where node $v$ has explicit degree $b_v$, budget $b^{*}_v = \nu(\mathrm{type}(v))$ and may be *closed*, meaning no further edge is attached to it. The source prints the neighbour mask

$$
M^{(t)}_{v,u} = \mathbb{1}(b_v < b^{*}_v) \cdot \mathbb{1}(b_u < b^{*}_u) \cdot \mathbb{1}(\text{no edge } v\text{--}u \text{ exists}) \cdot \mathbb{1}(v \neq u) \cdot \mathbb{1}(u \text{ is not closed})
$$

and the label mask

$$
m^{(t)}_{v,u,\ell} = M^{(t)}_{v,u} \cdot \mathbb{1}(b^{*}_u - b_u \le \ell) , \qquad \ell \in \{1,2,3\} ,
$$

each applied to its own softmax, so that the neighbour choice and the order choice are normalized separately; the stop option is never masked.

The printed label mask admits over-valence. With residual budgets $1$ and $1$ the neighbour mask passes and $\ell = 3$ satisfies $b^{*}_u - b_u = 1 \le 3$, so a triple bond can be drawn where one unit is available at each end; with residuals $1$ and $2$, reversing the inequality at the target would still admit $\ell = 2$. Hydrogen saturation cannot remove an edge already drawn.

**Two-sided restriction.** Replace the label mask by

$$
\widehat{m}^{(t)}_{v,u,\ell} = M^{(t)}_{v,u} \cdot \mathbb{1}\big(\ell \le \min(b^{*}_v - b_v,\; b^{*}_u - b_u)\big) .
$$

If the generation starts from a $\nu$-admissible partial graph, in particular from the empty graph or from the source's seeded node set with no edges, then every graph reachable under $\widehat{m}$ is $\nu$-admissible. The restriction is local: it constrains one transition, and it cannot repair an inadmissible starting graph, which is reachable at step zero and may be returned unchanged.

Two normalizers must be positive for the step to be defined. The neighbour softmax is positive whenever the always-available stop option carries positive weight. The order softmax is positive because a neighbour $u$ passing $M^{(t)}_{v,u}$ has $b_u < b^{*}_u$ and $b_v < b^{*}_v$, so $\ell = 1$ satisfies $\widehat{m}$, provided the sampling law gives positive weight to allowed choices. For termination, the current node is closed when the stop option is drawn and is not reopened, so each node is processed once and the finite node set bounds the run; leftover budget is then filled with hydrogen under a hydrogen convention.

## Depends on

- [Molecular graphs under valence constraints](molecular-graphs-under-valence-constraints.md)

## Proof depends on

None.

## Expansion

A formal development defines the generator state (typed nodes, edges with orders, the closed set), the neighbour and order masks, and the step relation that renormalizes each masked softmax over its allowed choices. The invariant $b_v \le b^{*}_v$ is proved by induction from an admissible initial graph: an added edge of order $\ell$ raises $b_v$ and $b_u$ by $\ell \le \min(b^{*}_v - b_v, b^{*}_u - b_u)$ under $\widehat{m}$, and closing a node changes no degree. Termination uses the close-on-stop policy and the finite node set.

## Context

Graduate. Liu, Allamanis, Brockschmidt and Gaunt introduce masking to keep a sequential graph generator inside the molecules; the two-sided restriction above is this page's correction of the printed label mask, not a statement of the source and not a claim about what any implementation does. Its string-based counterpart in this chapter is the SELFIES grammar.

## Sources

- Qi Liu, Miltiadis Allamanis, Marc Brockschmidt and Alexander L. Gaunt, *Constrained Graph Variational Autoencoders for Molecule Design*, Advances in Neural Information Processing Systems 31 (2018), Section 3 for the seeded generation with separately normalized masked softmaxes, and the valency-masking section for both printed masks and the hydrogen-saturation convention. arXiv:[1805.09076v2](https://arxiv.org/abs/1805.09076v2).
