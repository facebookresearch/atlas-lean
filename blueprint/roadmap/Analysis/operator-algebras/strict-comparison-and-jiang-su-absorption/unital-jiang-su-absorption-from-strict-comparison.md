# Jiang–Su absorption for unital algebras with strict comparison

Let $A$ be a nonzero, separable, unital complex $C^*$-algebra in the small universe, with a compatible star order. Suppose it has no nontrivial norm-closed two-sided ideals, is infinite-dimensional over $\mathbb C$, and is nuclear in the sense that for every small-universe unital complex $C^*$-algebra $B$, there is at most one $C^*$-norm on $A\odot B$. Assume the [strict comparison condition on the stabilization](strict-comparison-of-tracial-ranks.md) for the unital model.

There is a complex star-algebra isomorphism from $A$ onto the [source spatial tensor product with the specified Jiang–Su limit](specified-jiang-su-limit-and-spatial-tensor.md). No trace-state existence assumption is imposed for this absorption assertion. In particular it includes the case of an empty tracial state space; the comparison condition is still the stated implication on positive elements of the stabilization.

## Depends on

- [Strict comparison of tracial ranks](strict-comparison-of-tracial-ranks.md).
- [Specific limit and spatial tensor model](specified-jiang-su-limit-and-spatial-tensor.md).

## Proof depends on

The positive-trace case needs a central dimension-drop embedding and absorption transfer in the spatial norm model. The empty-trace case needs the separate empty-trace comparison bridge and the absorption argument for that case.

## Expansion

Split the proof into the trace-present and trace-empty cases. In both cases verify that the absorption target is the same choice-based inductive limit and spatial tensor closure, not an arbitrary model merely with the same name.

## Sources

- OpenAI Math, [`unital_main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Main.lean#L107-L115).
- [Family scope and accompanying paper](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/291.md).
- [Model definition, `Main.lean:30–51`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Main.lean#L30-L51).
- [Model definition, `Model.lean:2025–2031`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2025-L2031).
