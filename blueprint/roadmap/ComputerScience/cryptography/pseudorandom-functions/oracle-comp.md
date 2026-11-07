# Adaptive oracle algorithms

For a type $X$ of queries, a type $Y$ of answers and a type
$\alpha$ of outputs, an adaptive deterministic oracle algorithm is an element of CSLib's free
monad over the polynomial functor of one oracle with queries $X$ and answers $Y$. It is built
inductively: it either stops with an output in $\alpha$, or asks a query $x \in X$ and continues
with an algorithm that depends on the answer $y \in Y$.
