# Uniform property Gamma for unital algebras with strict comparison

Let $A$ be a nonzero, separable, unital complex $C^*$-algebra in the small universe, with a compatible star order. Suppose it has no nontrivial norm-closed two-sided ideals, is infinite-dimensional over $\mathbb C$, and is nuclear in the sense that for every small-universe unital complex $C^*$-algebra $B$, there is at most one $C^*$-norm on $A\odot B$. Assume the [strict comparison condition on the stabilization](strict-comparison-of-tracial-ranks.md) for the unital model.

If its tracial state space is nonempty, then for each specified free ultrafilter $\omega$ on $\mathbb N$, $A$ has the [uniform trace-splitting property](uniform-tracial-quotient-and-trace-splitting.md) in its uniform tracial ultrapower. In particular it splits into $m$ projections for **every** positive integer $m$ and the identities are tested on each constant image from $A$ against every trace coming from a sequence of tracial states. This clause is conditional on having a tracial state; the accompanying absorption clause is not.

## Depends on

- [Strict comparison of tracial ranks](strict-comparison-of-tracial-ranks.md).
- [Uniform tracial quotient and trace splitting](uniform-tracial-quotient-and-trace-splitting.md).

## Proof depends on

From strict comparison produce the tracial packing and central trace-splitting estimates for every $m$, with constants and representatives controlled uniformly over the traces.

## Expansion

Build the finite trace-splitting data and prove compatibility with the quotient and all sequence traces. The real-rank-zero halving result is about a different input algebra and does not provide this all-$m$ conclusion here.

## Sources

- OpenAI Math, [`unital_main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Main.lean#L107-L115).
- [Family scope and accompanying paper](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/291.md).
- [Model definition, `Model.lean:2025–2031`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2025-L2031).
- [Model definition, `Model.lean:2033–2042`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2033-L2042).
