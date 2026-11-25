# Substitution respects pointwise equality

Let $\sigma, \sigma'$ be parallel substitutions,
each sending every de Bruijn index to a term of the simply typed lambda calculus with references,
with $\sigma(x) = \sigma'(x)$ for every $x \in \mathbb{N}$. Then for every term $t$, applying
$\sigma$ to $t$ gives the same term as applying $\sigma'$ to $t$.
