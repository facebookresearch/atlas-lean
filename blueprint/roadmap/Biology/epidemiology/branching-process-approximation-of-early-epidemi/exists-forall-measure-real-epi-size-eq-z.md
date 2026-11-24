# For R₀ ≤ 1 and offspring numbers not always 1, outbreaks stay minor uniformly in the population

Let `ν` be a probability measure on `ℕ` (the offspring law) with
[mean](../../../Probability/branching-processes/galton-watson-process/mean.md) `R₀ = ∑_k k ν({k})`,
a value in `[0, ∞]`, and suppose `R₀ ≤ 1` and `ν({1}) ≠ 1`. Then for every `ε > 0` there is a number
of generations `n₀` such that for every `n ≥ n₀`, every measure `P` on a measurable space `Ω`, every
[offspring family](is-offspring-family.md) `ξ` under `P` with law `ν`, every type `α` of
individuals, all contact targets `U_j : Ω → α` (no law or measurability is assumed) and every finite
set `S₀ ⊆ α` of initially susceptible individuals, `P(I_n = 0) > 1 − ε`, where `I_n` is the
[number of infectives](epi-size.md) of generation `n` and `P` of the event `{I_n = 0}`, whose
measurability is not assumed, is its outer measure. The number `n₀` depends only on `ν` and `ε`.
