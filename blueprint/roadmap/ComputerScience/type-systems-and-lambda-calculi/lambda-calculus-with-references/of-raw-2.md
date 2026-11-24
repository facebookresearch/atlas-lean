# Typing is preserved by the embedding of raw STLC terms

Fix a type $B$ of base types,
and write $\iota$ for the embeddings of simple types and of raw terms of the simply typed
lambda calculus over $B$ into types and terms of the calculus with references over $B$. Let
$\Gamma$ be a context of simple types, $t$ a raw term and $A$ a simple type such that $t$ has
type $A$ in $\Gamma$. Then for every store typing $S$ we have
$\iota(\Gamma) \mid S \vdash \iota(t) : \iota(A)$, where $\iota(\Gamma)$ is the context
obtained by applying $\iota$ to each entry of $\Gamma$.
