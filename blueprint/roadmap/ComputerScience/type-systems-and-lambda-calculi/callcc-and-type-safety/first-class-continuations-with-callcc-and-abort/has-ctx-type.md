# Typing of evaluation contexts

For an answer type `T` and a context `Γ`,
`HasCtxType T Γ E A B` holds when plugging a term of type `A` into `E` gives a term of type `B`:
the empty context has type `A` to `A`, and each frame types its other subterms and passes the
type of the filled frame to the rest of the context.
