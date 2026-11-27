# Typing of embedded intrinsically typed STLC terms

Fix a type $B$ of base types, and
write $\iota$ for the embeddings of simple types and of raw terms of the simply typed lambda
calculus over $B$ into types and terms of the calculus with references over $B$. Let $\Gamma$ be
a context of simple types, $A$ a simple type and $t$ an intrinsically typed term of type $A$ in
$\Gamma$, and let $\mathrm{erase}(t)$ be the raw term obtained from $t$ by erasing its typing
information while keeping binder annotations. Then for every store typing $S$ we have
$\iota(\Gamma) \mid S \vdash \iota(\mathrm{erase}(t)) : \iota(A)$, where $\iota(\Gamma)$ is the
context obtained by applying $\iota$ to each entry of $\Gamma$.
