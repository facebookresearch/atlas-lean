# Call-by-name CPS translation of types

Fix an answer type $R$ of the simply typed lambda
calculus. The call-by-name CPS translation $A^\ast$ of a simple type $A$ is defined by recursion
on $A$: a base type is translated to itself, $b^\ast = b$, and a function type is translated by
$(A \to B)^\ast = ((A^\ast \to R) \to R) \to ((B^\ast \to R) \to R)$.
