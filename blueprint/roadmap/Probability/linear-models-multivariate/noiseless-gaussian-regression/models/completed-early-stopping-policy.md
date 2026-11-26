# Completed-rule Gaussian policies and prior-dependent admissibility

The rule at each seed specifies a finite initial distribution on a stop bit and a state, transition probabilities of those same actions from current state and exact labelled row, and a probability measure of unit outputs at each time/state. Recursively sum the transition probabilities times the continuation value, evaluating the output test immediately on stopping or at the horizon. The completed rule assumption is almost-everywhere measurability of each transition atom for Gaussian row times Lebesgue label, for almost every seed. For a prior, require additionally that, for every measurable nonnegative signal/output test bounded by one, the iterated test value is almost-everywhere measurable under the prior–(seed–rows) product probability. Success is the nonnegative lower integral of the iterated angle or chord event under this product. Model-admissibility at every prior is a separate hypothesis. The cube prior samples the uniform half-side cube and maps it to the unit sphere with coordinates $(u_i,\sqrt{1-u_i^2})$ scaled by $1/\sqrt n$, padding with zero if needed.

## Sources

- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MemoryPrecision.lean#L11-L127)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MemoryPrecision.lean#L316-L410)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MemoryPrecision.lean#L485-L486)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MemoryPrecision.lean#L719-L733)
