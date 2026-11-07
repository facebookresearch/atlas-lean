# CPS translation of variables

Fix an answer type $R$ and write $\overline{A}$ for the
call-by-value CPS translation of a type $A$. A de Bruijn variable of type $A$ in a context
$A_1, \ldots, A_n$ is sent to the variable at the same position in the translated context
$\overline{A_1}, \ldots, \overline{A_n}$, which has type $\overline{A}$.
