# The locally nameless STLC has the structural properties

CSLib's locally nameless
simply typed λ-calculus satisfies `StructuralTyping` with binding `⟨x, σ⟩ :: Γ`, instantiation
`t[x := s]`, the extension of `Γ` to every well-formed context `Δ` that is a permutation of
`Γ ++ Θ` for some `Θ`, and the identity action of weakening on terms. Substitution is CSLib's
`Typing.typing_subst_head`; weakening combines `Typing.weaken`, whose well-formedness side
condition the extension relation carries, with `Typing.perm`.
