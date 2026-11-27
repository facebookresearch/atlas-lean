# Uniform property Gamma for stably projectionless algebras

Let $A$ be a nonzero separable complex $C^*$-algebra in the small universe, not necessarily unital, with a compatible star order and no nontrivial norm-closed two-sided ideals. Its stabilization in the [finite-matrix model](strict-comparison-of-tracial-ranks.md) has no nonzero self-adjoint projections. Assume the space of positive linear norm-one tracial functionals on $A$ is nonempty and compact in the weak-* topology induced by their underlying continuous functionals. Assume every densely finite lower-semicontinuous extended trace is bounded on positive contractions, and the [finite-target-rank strict comparison condition](strict-comparison-of-tracial-ranks.md) holds. Assume that for every small-universe unital complex $C^*$-algebra $B$, there is at most one nonunital $C^*$-norm on $A\odot B$.

For each specified free ultrafilter $\omega$ on $\mathbb N$, there is [uniform trace splitting](uniform-tracial-quotient-and-trace-splitting.md) of every positive finite order. Use the quotient of bounded sequences in the unitization by the uniform two-norm of the unitized normalized traces. The projections sum to the quotient unit and commute with the constant images of $A$ (not an extra family of arbitrary elements); the trace identities test those constant images against every sequence of normalized traces on $A$, extended to the unitization.

## Depends on

- [Stabilization, trace-base and comparison conventions](strict-comparison-of-tracial-ranks.md).
- [Uniform tracial quotient and trace splitting](uniform-tracial-quotient-and-trace-splitting.md).

## Proof depends on

The finite-target-rank comparison must yield uniform cut and packing estimates with the compact normalized trace base, and the resulting projections must be central and equally trace-splitting for all sequence traces in the specified quotient.

## Expansion

Separate trace extension and compact-base uniformity from central projective splitting. Keep the test on the image of the nonunital algebra and the unit in the larger quotient.

## Sources

- OpenAI Math, [`stably_projectionless_main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Main.lean#L140-L158).
- [Family scope and accompanying paper](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/291.md).
- [Model definition, `Model.lean:2513–2550`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2513-L2550).
- [Model definition, `Model.lean:2554–2579`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2554-L2579).
