# Kripke realization relation for NbE

Fix an interpretation $I$ of the base types. For a
context $\Gamma$, an environment $\eta$ for $\Gamma$ in $I$, a type $A$, a Kripke semantic value
$v$ of type $A$ in $\Gamma$ and an element $d$ of the denotation of $A$ under $I$, the relation
"$v$ realizes $d$ at $\eta$" is defined by recursion on $A$. At a base type, $v$ is a neutral
term, and $v$ realizes $d$ when the denotation of $v$, read as a term, in $\eta$ equals $d$. At a
function type $A \Rightarrow B$, $v$ realizes $d$ when for every context $\Delta$, every renaming
$\rho : \Gamma \to \Delta$, every environment $\theta$ for $\Delta$ with $\theta \circ \rho = \eta$,
every semantic value $a$ of type $A$ in $\Delta$ and every element $e$ of the denotation of $A$
such that $a$ realizes $e$ at $\theta$, the semantic value $v(\rho, a)$ realizes $d(e)$ at
$\theta$.
