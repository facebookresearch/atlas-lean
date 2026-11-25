# The lambda calculus with references has the structural properties

The simply typed
λ-calculus with references satisfies `StructuralTyping` when a context pairs a variable context
`Γ` with a store typing `S`: binding adds a new innermost de Bruijn variable to `Γ`;
instantiation is `Term.instantiate`; `(Γ, S)` extends to `(Δ, S')` when `Δ = Θ ++ Γ` for a block
`Θ` of new innermost variables and `S` is a prefix of `S'`; and weakening shifts every free
variable by the length of `Θ`. Substitution is `HasType.instantiate`; weakening combines
`HasType.rename` with `HasType.extendStore`.
