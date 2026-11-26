# The calculus with exceptions has the structural properties

For every exception type
`exn`, the typing judgment satisfies `TypeSafety.StructuralTyping` when binding adds a new
innermost variable, instantiation is `Term.instantiate`, a context `Γ` extends to `Θ ++ Γ` for
every block `Θ` of new innermost variables, and weakening raises every free variable by the
difference of the context lengths.
