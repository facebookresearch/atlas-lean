# Denotational correctness of the call-by-name CPS translation

Fix an answer type $R$ and
an interpretation of the base types; write $D(A)$ for the set of values of a simple type $A$,
$A^\ast$ for its call-by-name CPS translation, and $\sim_A$ for the call-by-name logical
relation. Let $t$ be a term of type $A$ in a context $\Gamma$, and let $\eta$ be an environment
for $\Gamma$ and $\eta'$ an environment for the translated context such that $\eta$ and $\eta'$
are related. Let $a \in D(A)$ be the denotation of $t$ in $\eta$, and let $c$ be the denotation
in $\eta'$ of the call-by-name CPS translation $\overline{t}$ of $t$. Then there is
$v \in D(A^\ast)$ with $a \sim_A v$ such that $c\,k = k\,v$ for every continuation
$k \in D(A^\ast \to R)$.
