# Related environments for the call-by-name CPS translation

Fix an answer type $R$ and an
interpretation of the base types, and write $C(A) = (A^\ast \to R) \to R$, where $A^\ast$ is the
call-by-name CPS translation of a simple type $A$. Let $\eta$ be an environment for a context
$\Gamma = A_1, \dots, A_n$, assigning to each variable $x$ of type $A$ a value $\eta(x)$ of type
$A$, and let $\eta'$ be an environment for the translated context $C(A_1), \dots, C(A_n)$. Then
$\eta$ and $\eta'$ are related when for every variable $x$ of $\Gamma$, of type $A$ say, the
value that $\eta'$ assigns to the variable at the same position as $x$ in the translated context
is a computation of type $C(A)$ related to $\eta(x)$.
