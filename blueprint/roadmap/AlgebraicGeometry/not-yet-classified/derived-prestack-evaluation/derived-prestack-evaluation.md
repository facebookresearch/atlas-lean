# The evaluation map of a mapping prestack

For a commutative ring $k$, a cofibrant
replacement functor $Q$ for simplicial commutative $k$-algebras, prestacks $X$ and $F$ over $k$ and
a fibrant replacement $R$ of $F$, with fibrant model $R(F)$: a morphism of prestacks
$\operatorname{Map}(X, F) \times X \to R(F)$ (`EvaluationModel`) from the product of the mapping
prestack `mappingPrestackFunctor k Q X F R` with $X$, whose value on every simplicial commutative
$k$-algebra $A$, simplicial degree $n$, mapping simplex $a$ and $x \in X(A)_n$ is the evaluation
`evaluateDegree`: the degree-$n$ component of the family $a$ at $A$, applied to the augmentation
$QA \to A$ and to $x$.
