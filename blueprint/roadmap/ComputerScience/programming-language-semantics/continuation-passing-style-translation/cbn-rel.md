# Logical relation for the call-by-name CPS translation

Fix an answer type $R$ and an
interpretation $I$ of the base types. Write $D(A)$ for the set of values of a simple type $A$
($D(b) = I(b)$ for a base type $b$, and $D(A \to B)$ is the set of functions from $D(A)$ to
$D(B)$), $A^\ast$ for the call-by-name CPS translation of $A$, and
$C(A) = (A^\ast \to R) \to R$. The relation $a \sim_A a'$ between $a \in D(A)$ and
$a' \in D(A^\ast)$ is defined by recursion on $A$. At a base type $b$, $a \sim_b a'$ holds when
$a = a'$. At a function type, $f \sim_{A \to B} g$ holds when for every $a \in D(A)$ and every
$c \in D(C(A))$: if there is $v$ with $a \sim_A v$ and $c\,k = k\,v$ for every
$k \in D(A^\ast \to R)$, then there is $w$ with $f\,a \sim_B w$ and $g\,c\,k = k\,w$ for every
$k \in D(B^\ast \to R)$.
