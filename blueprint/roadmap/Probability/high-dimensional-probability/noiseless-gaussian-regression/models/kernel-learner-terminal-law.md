# Finite kernel learner and terminal-tagged success

A finite rule assigns probability measures on a Boolean stop bit and state initially and after each exact labelled row, and a probability measure of unit outputs at each terminal time/state. A stop at time zero or at a transition tags the state permanently; an active run reaching the horizon receives terminal time $T$. For each fixed seed, signal and row array iterate the finite-action kernel and bind the terminal output measure, retaining the terminal tag. For each seed integrate the mass of angular success, with or without a specified terminal tag, over the sphere–rows product. Then lower-integrate those values over the seed law. No joint measurability of the full experiment follows from per-seed completion. In the separate pointwise branch the fixed-signal lower integral uses seed–rows, and the source assumes joint almost-everywhere measurability there. The power-of-two state count and reference Gaussian-row times Lebesgue-label space do not by themselves equate this rule with a deterministic seeded learner.

## Sources

- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ProjectionMoments.lean#L120-L310)
