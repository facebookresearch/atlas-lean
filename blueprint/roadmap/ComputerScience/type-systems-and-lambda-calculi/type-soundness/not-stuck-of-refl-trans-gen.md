# Typed states never reach a stuck state

Let `Step` be a one-step relation on states,
`Final` a predicate on states that need not be terminal, and `HasType s A` a typing predicate.
Assume progress, every typed state is final or steps, and preservation, every step from a state
of type `A` reaches a state of type `A`. Then every state reachable from a typed state is not
stuck, that is, it is not a non-final normal form.

## Sources

- Software Foundations, `StlcProp`, `Corollary type_soundness`, where `stuck t := normal_form step t ∧ ¬ value t`.
