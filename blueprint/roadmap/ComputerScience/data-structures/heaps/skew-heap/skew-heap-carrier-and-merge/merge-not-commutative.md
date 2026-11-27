# Merge not commutative

Non-vacuity checks: concrete counterexamples showing the
definitions are not trivial / vacuous (e.g. `merge` is not
commutative, `heap` is not always true, `Phi` is not always `0`).
These are proved theorems, not random tests: the `plausible` tactic
cannot be used for this out of the box, because it needs
`SampleableExt` instances for the custom `Tree` type and decidable
predicates (`heap` is a `Prop`, not `Decidable`), and deriving those
instances in this file would pollute the development.
