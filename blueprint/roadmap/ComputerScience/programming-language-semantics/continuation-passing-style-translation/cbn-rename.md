# The call-by-name CPS translation commutes with renaming

Fix an answer type $R$ and write
$\overline{t}$ for the call-by-name CPS translation of a term $t$. For a renaming $\rho$ from a
context $\Gamma$ to a context $\Delta$, let $\overline{\rho}$ be the renaming of the translated
contexts that sends the translation of each variable $x$ of $\Gamma$ to the translation of
$\rho(x)$. Then for every term $t$ in context $\Gamma$, the translation of the renamed term
$t[\rho]$ is the renaming of $\overline{t}$ by $\overline{\rho}$:
$\overline{t[\rho]} = \overline{t}[\overline{\rho}]$.
