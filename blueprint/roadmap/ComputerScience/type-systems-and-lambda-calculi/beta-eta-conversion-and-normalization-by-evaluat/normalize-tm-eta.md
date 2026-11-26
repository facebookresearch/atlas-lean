# Normalized terms of an eta-expansion and its function coincide

Work in the intrinsically typed simply typed lambda calculus over a type of base types, with de Bruijn variables: the terms of type $A$ in a context $\Gamma$ (a list of simple types) are variables, applications $f\,a$ and abstractions $\lambda t$, whose body $t$ lies in $A :: \Gamma$, the context $\Gamma$ extended by a newest variable $0$ of type $A$.

Normalization by evaluation sends a term $t$ of type $A$ in $\Gamma$ to its normal form $\mathrm{nf}(t)$, a beta-normal, eta-long normal form of type $A$ in $\Gamma$ (an element of the separate type of normal forms), obtained by evaluating $t$ in the Kripke semantic domain at the identity environment, which reflects each variable as itself, and reifying the result at type $A$. The normalized term $\mathrm{nf}_{\mathrm{Tm}}(t)$ is the term underlying $\mathrm{nf}(t)$. For a term $t$ in $A :: \Gamma$ and a term $a$ of type $A$ in $\Gamma$, the instantiation $t[a]$ substitutes $a$ for the newest variable and replaces each older variable $x+1$ by $x$; for a term $f$ in $\Gamma$, the weakening $f^{\uparrow}$ is $f$ with every variable renamed to its successor.

For every term $f$ of type $A \Rightarrow B$ in $\Gamma$, with $f^{\uparrow}$ its weakening into $A :: \Gamma$ and $0$ the newest variable of type $A$,

$$\mathrm{nf}_{\mathrm{Tm}}(\lambda(f^{\uparrow}\,0)) = \mathrm{nf}_{\mathrm{Tm}}(f).$$
