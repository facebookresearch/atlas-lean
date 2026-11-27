# Normalization by evaluation identifies a beta-redex with its contractum

Work in the intrinsically typed simply typed lambda calculus over a type of base types, with de Bruijn variables: the terms of type $A$ in a context $\Gamma$ (a list of simple types) are the variables of type $A$, the applications $f\,a$ of a term $f$ of type $D \Rightarrow A$ to a term $a$ of type $D$, both in $\Gamma$, and, when $A = D \Rightarrow E$, the abstractions $\lambda t$ whose body $t$ is a term of type $E$ in $D :: \Gamma$, the context $\Gamma$ extended by a newest variable $0$ of type $D$.

Normalization by evaluation sends a term $t$ of type $A$ in $\Gamma$ to its normal form $\mathrm{nf}(t)$, a beta-normal, eta-long normal form of type $A$ in $\Gamma$ (an element of the separate type of normal forms), obtained by evaluating $t$ in the Kripke semantic domain at the identity environment, which reflects each variable as itself, and reifying the result at type $A$. For a term $t$ in $A :: \Gamma$ and a term $a$ of type $A$ in $\Gamma$, the instantiation $t[a]$ substitutes $a$ for the newest variable and replaces each older variable $x+1$ by $x$; for a term $f$ in $\Gamma$, the weakening $f^{\uparrow}$ is $f$ with every variable renamed to its successor.

For every term $t$ of type $B$ in $A :: \Gamma$ and every term $a$ of type $A$ in $\Gamma$, the normal forms of the beta-redex and of its contractum are equal:

$$\mathrm{nf}((\lambda t)\,a) = \mathrm{nf}(t[a]).$$
