# Related environments

Fix an answer type $R$ and an interpretation $I$ of the base types,
and write $\overline{\Gamma}$ for the context obtained by translating each type of a context
$\Gamma$ by the call-by-value CPS translation. An environment $\eta$ for $\Gamma$ and an
environment $\eta'$ for $\overline{\Gamma}$ are related when, for every variable $x$ of type $A$
in $\Gamma$, the value $\eta(x)$ is related at type $A$, by the CPS logical relation, to the value
that $\eta'$ assigns to the variable at the same position in $\overline{\Gamma}$.
