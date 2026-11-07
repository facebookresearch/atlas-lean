# Realization of environments

Fix an interpretation $I$ of the base types, contexts
$\Delta$ and $\Gamma$, an environment $\theta$ for $\Delta$ in $I$, a Kripke semantic environment
$\xi$ assigning to each variable of $\Gamma$ a semantic value in $\Delta$, and an environment
$\eta$ for $\Gamma$ in $I$. Then $\xi$ realizes $\eta$ at $\theta$ when for every type $A$ and
every variable $x$ of type $A$ in $\Gamma$, the semantic value $\xi(x)$ realizes $\eta(x)$ at
$\theta$.
