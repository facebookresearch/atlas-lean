# Rank-one projector set with no ten smaller-diameter pieces

Let $P=\{uu^{\mathsf T}:u\in\mathbb R^4,\|u\|_2=1\}$ in the space of real $4\times4$ matrices with Frobenius distance. Then $P$ is compact, is contained in the affine space of symmetric matrices of trace one, and has diameter $\sqrt2$. No ten sets $C_1,\dots,C_{10}$ with each $C_i\subseteq P$ and $P\subseteq\bigcup_iC_i$ have all diameters strictly below $\sqrt2$. The ambient affine space is nine-dimensional; the assertion neither selects a finite witness nor asserts the least failure dimension.

## Depends on

- [Borsuk cover predicate](has-borsuk-cover.md)
- Rank-one projectors in the Frobenius model and the trace-one affine isometry to nine-space.

## Proof depends on

- Cover obstruction for arbitrary pieces; elementary compactness, trace and diameter formulas.

## Expansion

Reuse the existing Borsuk cover predicate only after checking its extended diameter and arbitrary-cover conventions against this fixed compact set. Derive the distance identity from $\|u\|=\|v\|=1$ and isolate the ten-piece obstruction; existing high-dimensional finite witnesses do not establish this one.

## Sources

- OpenAI Math, [`main_theorem`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BorsukNine.lean#L25-L31) (statement and local definitions).
