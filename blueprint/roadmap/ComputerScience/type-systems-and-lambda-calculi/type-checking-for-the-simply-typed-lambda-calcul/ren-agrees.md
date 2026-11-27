# Agreement of a typed and a numerical renaming

A typed renaming $\rho$ from context
$\Gamma$ to context $\Delta$ agrees with a map $r : \mathbb{N} \to \mathbb{N}$ when, for every
type $A$ and every variable $x$ of type $A$ in $\Gamma$, the de Bruijn index of $\rho(x)$
equals $r$ applied to the de Bruijn index of $x$.
