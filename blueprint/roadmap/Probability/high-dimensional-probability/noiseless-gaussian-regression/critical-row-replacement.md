# Gaussian row replacement at the critical block width

For a joint law $Q$ of a unit signal $S$, a message $W$ and a row array $G$, define its exposed information as $I_Q(S;W\mid G,GS)$, the KL after disintegrating over the row-label pair and replacing the two conditional marginals by their product. Begin with a probability law $P$ of $(S,W,X)$, with $S$ uniform on the unit sphere, $W$ countable with measurable singletons, and the marginal $(S,X)$ equal to uniform sphere times independent standard Gaussian rows of width $\lfloor d/10\rfloor$. Assume $H(W)\le d^2$ in nats. Compare two row arrays: actual $G=(X,Z)$ with $\lfloor d/2\rfloor-\lfloor d/10\rfloor$ independent fresh rows $Z$, and a fully fresh $G$ of that same total width independent of $(S,W)$. In both cases use the exact labels $GS$ of those rows. There are absolute $K>0$ and $d_0$ such that for all $d\ge d_0$, fresh exposed information is at most actual exposed information plus $Kd$.

**Conventions.** Use the conditional information and exact row-label law, and the distinction between $(S,X)$ independent and $(S,W,X)$ potentially coupled.

## Depends on

- [Conditional information from marginal kernels](conditional-information-from-marginal-kernels.md)
- [Noiseless Gaussian row and label density models](gaussian-projection-density-model.md)

## Proof depends on

A quantitative actual-to-fresh comparison with the fixed entropy budget and the prescribed width split.

## Expansion

Specify both joint laws as pushforwards, justify the conditional KL definition, and prove the information loss bound rather than comparing the labels alone. Keep the original width and the truncating natural divisions.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L502-L504)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Replacing Gaussian observations in memory-constrained inference](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf)
