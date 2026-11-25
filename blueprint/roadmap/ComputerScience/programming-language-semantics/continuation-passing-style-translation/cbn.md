# Call-by-name CPS translation of terms

Fix an answer type $R$ and write
$C(A) = (A^\ast \to R) \to R$, where $A^\ast$ is the call-by-name CPS translation of a simple
type $A$. A term $t$ of type $A$ in a context $A_1, \dots, A_n$ is translated to a term
$\overline{t}$ of type $C(A)$ in the context $C(A_1), \dots, C(A_n)$, by recursion on $t$: a
variable $x$ is translated to the variable at the same position; an abstraction by
$\overline{\lambda x.\, M} = \lambda k.\, k\,(\lambda x.\, \overline{M})$; and an application by
$\overline{M\,N} = \lambda k.\, \overline{M}\,(\lambda m.\, m\,\overline{N}\,k)$, where $k$ and
$m$ are fresh variables.
