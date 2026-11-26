# Term

Locally nameless terms over free names `Var`. In the notes' syntax: `abs` is `λx. e`,
`pair` is the tensor pair `⟨e₁, e₂⟩`, `casePair t u` is `case t (⟨x, y⟩ ⇒ u)`, `unit` is `⟨⟩`,
`caseUnit t u` is `case t (⟨⟩ ⇒ u)`, `lpair` is `⟨|e₁, e₂|⟩`, `proj₁` and `proj₂` are the
projections, `inl` and `inr` are `l · e` and `r · e`, `casePlus t u v` is
`case t (l · x ⇒ u | r · y ⇒ v)`, `lunit` is `⟨| |⟩` and `caseZero t` is `case t ( )`.
