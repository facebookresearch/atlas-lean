# Triple trace iff

Let `F` be a functor from a category with a symmetric trace `T` to monotone relations that preserves `T` with respect to the existential trace. For `f : X ⊗ U ⟶ Y ⊗ U` and assertions `P`, `Q`, the Hoare triple `{P} trace f {Q}` holds if and only if some invariant assertion `I` on `U` satisfies the tensor triple `{(P, I)} f {(Q, I)}`.
