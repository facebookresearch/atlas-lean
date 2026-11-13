# PRDS on `H0`

**PRDS on `H0`** (Benjamini–Yekutieli 2001, §2.2), stated for the p-value vector
`P = (p 0, …, p (m - 1))`: for every true null `i ∈ H0` and every measurable increasing set
`D ⊆ ℝ^m` (`IsUpperSet D` for the coordinatewise order), the conditional probability
`x ↦ P(P ∈ D | p i = x)` has a nondecreasing version. The conditional probability is Mathlib's
regular conditional distribution `condDistrib P (p i) μ`, which is determined only up to
`μ.map (p i)`-null sets, hence the "version" (`=ᵐ`) quantifier. Larger p-values are less
significant, so `D` increasing means "closed under making p-values larger".
