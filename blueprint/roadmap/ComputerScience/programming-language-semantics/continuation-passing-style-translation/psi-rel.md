# Plotkin's value translation $\Psi$

Fix an answer type $R$, and write $A^*$ for the
call-by-value CPS translation of a type $A$, $\Gamma^*$ for the context obtained by translating
each type of a context $\Gamma$, and $\overline{M}$ for the CPS translation of a term $M$. The
relation $\Psi$ between terms of type $A$ in context $\Gamma$ and terms of type $A^*$ in context
$\Gamma^*$ holds in exactly two cases: a variable $x$ of $\Gamma$ is related to the variable at
the same position in $\Gamma^*$, and an abstraction $\lambda x.\, N$ is related to
$\lambda x.\, \overline{N}$.
