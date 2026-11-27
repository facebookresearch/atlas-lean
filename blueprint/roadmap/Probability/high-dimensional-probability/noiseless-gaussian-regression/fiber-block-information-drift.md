# Fiber information drift across a Gaussian block

Start with a joint probability $P$ of uniform unit signal $S$ and finite singleton-measurable state $U$. Update to a finite singleton-measurable state $V$ by any Markov kernel of the state, $\lfloor d/10\rfloor$ fresh independent standard Gaussian rows and their exact signal labels. If $N\ge1$, $|V|\le N$ and $\log N\le d^2$, then for absolute $K>0,d_0$ and $d\ge d_0$,

$$
I_{\lfloor d/3\rfloor}(S;V)\le I_{\lfloor d/3\rfloor}(S;U)+Kd,
$$

where $I_k(S;A)$ denotes $I(S;A\mid G,GS)$ with $k$ entirely fresh independent rows relative to the stated law of the signal and state. These are extended nonnegative quantities.

**Conventions.** Use the [fresh exposed information](conditional-information-from-marginal-kernels.md) at the fixed width $\lfloor d/3\rfloor$, not a width average.

## Depends on

- [Conditional information from marginal kernels](conditional-information-from-marginal-kernels.md)
- [Noiseless Gaussian row and label density models](gaussian-projection-density-model.md)

## Proof depends on

- [The exact spherical two-point measure identity](spherical-fiber-two-point-measure.md)

The update also needs conditional fiber comparison and information control under the actual Gaussian rows.

Use the same spherical signal marginal on both sides, and track fresh probe rows separately from rows consumed by the transition. Bound the change from the fiber estimates without passing to a real projection or replacing the outgoing alphabet bound by one on the incoming state.

## Expansion

Identify the conditional fiber comparison for the actual row/label law and the width-specific finite-state information bound before deriving the drift. Do not use the width average in place of the width fixed here.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L517-L519)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Replacing Gaussian observations in memory-constrained inference](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf)
- [Pinned experiment definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L335-L344)
