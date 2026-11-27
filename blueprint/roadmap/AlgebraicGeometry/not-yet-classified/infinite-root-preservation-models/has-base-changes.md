# Has Base Changes

Base changes of the stack $R$ over $S$ are stacks: an instance of this class asserts that, for
every morphism of schemes $b : T \to S$, the base change of $R$ along $b$, obtained by composing $R$
with the functor from schemes over $T$ to schemes over $S$ induced by $b$
(`RootEtaleRestrictions.pseudofunctor b R`), is a stack for the fppf topology over $T$.
