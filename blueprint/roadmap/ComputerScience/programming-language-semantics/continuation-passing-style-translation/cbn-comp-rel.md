# Related computations in the call-by-name CPS translation

Fix an answer type $R$ and an
interpretation $I$ of the base types; write $D(A)$ for the set of values of a simple type $A$,
$A^\ast$ for its call-by-name CPS translation, $C(A) = (A^\ast \to R) \to R$, and $\sim_A$ for
the call-by-name logical relation between $D(A)$ and $D(A^\ast)$. A computation $c \in D(C(A))$
is related to a value $a \in D(A)$ when there is $v \in D(A^\ast)$ with $a \sim_A v$ such that
$c\,k = k\,v$ for every continuation $k \in D(A^\ast \to R)$.
