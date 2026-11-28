# Typing of the continuation of a context

Let `T` be the answer type and `Γ` a context.
If the context `E` has type `A` to `T` in `Γ`, then for every type `B` its continuation
`λx. abort E[x]` has type `A → B` in `Γ`.
