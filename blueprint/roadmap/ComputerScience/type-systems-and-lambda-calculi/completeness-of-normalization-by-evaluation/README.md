# Completeness of normalization by evaluation

Normalization by evaluation for the simply typed lambda calculus is complete for beta-eta
conversion: two terms are convertible exactly when their normal forms agree. The proof uses two
logical relations on Kripke semantic values: relatedness of semantic values, under which evaluation
commutes with substitution, and a relation between semantic values and terms, under which every
term is convertible to its normal form.

- [Logical relatedness of semantic values](related.md)
- [Logical semantic values](logical.md)
- [Logical semantic values are related to themselves](related-refl.md)
- [Logical semantic values are natural](natural.md)
- [A natural semantic value related to itself is logical](of-natural-related-refl.md)
- [Related semantic functions send related arguments to related values](app.md)
- [A logical semantic function sends logical arguments to logical values](app-2.md)
- [Reflection is logical and reification respects relatedness](reflect-logical-quote-related.md)
- [Reflected neutral terms are logical](reflect-logical.md)
- [Reification identifies related semantic values](quote-eq-of-related.md)
- [Renaming preserves logicality and relatedness](logical-rename-related-rename.md)
- [Logical semantic environments](logical-2.md)
- [Related semantic environments](related-2.md)
- [Fundamental theorem of the logical relation for NbE evaluation](nbe-eval-logical-related.md)
- [Evaluating a lifted substitution](eval-sub-lift-related.md)
- [Evaluation after a substitution](nbe-eval-subst-related.md)
- [The normal form after a substitution](normalize-nf-subst.md)
- [The normalized term after a substitution](normalize-tm-subst.md)
- [The normal form of a beta instantiation](normalize-nf-instantiate.md)
- [The normalized term of a beta instantiation](normalize-tm-instantiate.md)
- [The syntactic logical relation between semantic values and terms](syntactic-related.md)
- [The syntactic logical relation respects beta-eta conversion](congr.md)
- [Reification of a syntactically related value](quote-syntactic.md)
- [Reflected neutral terms are related to their terms](reflect-syntactic.md)
- [Semantic environments related to substitutions](syntactically-related.md)
- [Extending a related environment and substitution by one variable](cons.md)
- [Renaming a related environment and substitution](rename.md)
- [Fundamental theorem of the syntactic logical relation](nbe-eval-syntactic.md)
- [The identity environment is related to the identity substitution](identity-syntactic.md)
- [Every term is beta-eta convertible to its normalized term](beta-eta-eq-normalize-tm.md)
- [Terms with equal normalized terms are beta-eta convertible](beta-eta-eq-of-normalize-tm-eq.md)
- [Beta-eta conversion is equality of normalized terms](beta-eta-eq-iff-normalize-tm-eq.md)
- [Terms with the same NbE normal form are beta-eta convertible](beta-eta-complete.md)
