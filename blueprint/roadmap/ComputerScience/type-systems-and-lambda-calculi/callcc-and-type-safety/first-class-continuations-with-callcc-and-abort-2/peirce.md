# Callcc has the type of Peirce's law

For every answer type `T`, context `Γ` and types
`A` and `B`, the term `λf. callcc f` has type `((A → B) → A) → A` in `Γ`.
