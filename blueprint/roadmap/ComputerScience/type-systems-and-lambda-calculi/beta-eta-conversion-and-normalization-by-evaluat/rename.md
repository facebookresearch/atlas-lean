# Renaming preserves beta-eta conversion

Work in the intrinsically typed simply typed lambda calculus over a type of base types, with de Bruijn variables: the terms of type $A$ in a context $\Gamma$ (a list of simple types) are the variables of type $A$, the applications $f\,a$ of a term $f$ of type $D \Rightarrow A$ to a term $a$ of type $D$, both in $\Gamma$, and, when $A = D \Rightarrow E$, the abstractions $\lambda t$ whose body $t$ is a term of type $E$ in $D :: \Gamma$, the context $\Gamma$ extended by a newest variable $0$ of type $D$.

For a term $t$ in $A :: \Gamma$ and a term $a$ of type $A$ in $\Gamma$, the instantiation $t[a]$ substitutes $a$ for the newest variable and replaces each older variable $x+1$ by $x$; for a term $f$ in $\Gamma$, the weakening $f^{\uparrow}$ is $f$ with every variable renamed to its successor. Beta-eta conversion $\simeq$ is the least relation between terms of the same type in the same context that is reflexive, symmetric and transitive, is closed under application ($f \simeq g$ and $a \simeq b$ give $f\,a \simeq g\,b$) and abstraction ($t \simeq t'$ gives $\lambda t \simeq \lambda t'$), and contains every beta instance $(\lambda t)\,a \simeq t[a]$ and every eta instance $\lambda(f^{\uparrow}\,0) \simeq f$.

A renaming $\rho$ from $\Gamma$ to $\Delta$ maps every variable of $\Gamma$ to a variable of $\Delta$ of the same type, and $t[\rho]$ renames every free variable of $t$ along $\rho$ (lifting $\rho$ under binders).

For terms $t, u$ of type $A$ in $\Gamma$ with $t \simeq u$ and every renaming $\rho$ from $\Gamma$ to $\Delta$, $t[\rho] \simeq u[\rho]$.
