# Under ∑ δ_θ = δ the equilibrium equations decouple by linkage class

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set `S` and finite reaction set `ρ` whose
[deficiency](../../../Dynamics/smooth-dynamics/deficiency.md) `δ` is the sum of the
[deficiencies `δ_θ` of its linkage classes](linkage-class-deficiency.md), `∑_θ δ_θ = δ`. Then for
all real rate constants `k ∈ ℝ^ρ` and all `x ∈ ℝ^S`, `x` is an equilibrium of the mass-action
system, `f(x) = 0`, if and only if `f_θ(x) = 0` for every linkage class `θ`, where `f` is the
[mass-action vector field](../../../Dynamics/smooth-dynamics/mass-action-field.md) and `f_θ` the
[mass-action field of `θ`](linkage-class-field.md), both with rate constants `k`. In the model the
rate constants are positive and the concentrations nonnegative; the equivalence holds for all real
`k` and `x`. The proof of Feinberg's deficiency-one theorem uses this reduction to single linkage
classes.

## Sources

- Feinberg (1995); Boros (2012); Feinberg (2019).
