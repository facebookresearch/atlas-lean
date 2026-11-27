# Jiang–Su absorption for stably projectionless algebras with strict comparison

Let $A$ be a nonzero separable complex $C^*$-algebra in the small universe, not necessarily unital, with a compatible star order and no nontrivial norm-closed two-sided ideals. Its stabilization in the [finite-matrix model](strict-comparison-of-tracial-ranks.md) has no nonzero self-adjoint projections. Assume the space of positive linear norm-one tracial functionals on $A$ is nonempty and compact in the weak-* topology induced by their underlying continuous functionals. Assume every densely finite lower-semicontinuous extended trace is bounded on positive contractions, and the [finite-target-rank strict comparison condition](strict-comparison-of-tracial-ranks.md) holds. Assume that for every small-universe unital complex $C^*$-algebra $B$, there is at most one nonunital $C^*$-norm on $A\odot B$.

There is a complex star-algebra isomorphism from $A$ onto the [source nonunital spatial tensor product with its specified Jiang–Su limit](specified-jiang-su-limit-and-spatial-tensor.md). This means the closed tensor ideal inside the spatial product formed using the unitization of $A$, not absorption of the unitization itself. It does not compare two algebras via a trace-cone equivalence.

## Depends on

- [Stabilization, trace-base and comparison conventions](strict-comparison-of-tracial-ranks.md).
- [Specific limit and nonunital spatial tensor model](specified-jiang-su-limit-and-spatial-tensor.md).

## Proof depends on

Use the finite-target-rank comparison transfer to a central dimension-drop system in the nonunital setting and prove absorption into the actual spatial tensor ideal.

## Expansion

Separate bounded trace extension and the matrix-limit rank comparison from the central construction and the norm-level isomorphism. Do not substitute an embedding or stable classification by a trace cone for the asserted isomorphism.

## Sources

- OpenAI Math, [`stably_projectionless_main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Main.lean#L140-L158).
- [Family scope and accompanying paper](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/291.md).
- [Model definition, `Main.lean:84–99`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Main.lean#L84-L99).
- [Model definition, `Model.lean:2513–2550`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2513-L2550).
