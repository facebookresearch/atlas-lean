# Deficiency-zero theorem, existence of a complex-balanced equilibrium

**Deficiency-zero theorem, existence of a complex-balanced equilibrium** (Horn 1972;
Feinberg 1972). A weakly reversible mass-action network of deficiency zero has, for any
positive rate constants, a positive complex-balanced equilibrium.

The two network hypotheses are stated in elementary form. `hwr` is weak reversibility: for
every reaction `y → y'` there is a directed path of reactions from `y'` back to `y`. `hδ` is
deficiency zero in its linear-algebra form `ker Y ∩ im ∂ = 0` (Feinberg 2019, §6.4): a
weighting `α` of the reactions with zero net stoichiometric change `∑ α r (prod r - src r)`
has zero net change on the complexes. That `δ = n - ℓ - s = 0` is equivalent to `hδ` is
`deficiency_eq_zero_iff` (in `MathlibExt.Biology.Dynamics.DeficiencyZero.Integration`), via the
rank identity `dim im ∂ = n - ℓ`. Rate constants must be strictly
positive; zero rates are excluded.

## Sources

- Horn (1972); Feinberg (1972); Feinberg (1987); Feinberg (2019), ch. 16.
