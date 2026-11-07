# Call-by-name CPS translation of variables

Fix an answer type $R$ and write
$C(A) = (A^\ast \to R) \to R$, where $A^\ast$ is the call-by-name CPS translation of a simple
type $A$. A variable of type $A$ in a context $A_1, \dots, A_n$ is translated to the variable at
the same position in the translated context $C(A_1), \dots, C(A_n)$, where it has type $C(A)$.
