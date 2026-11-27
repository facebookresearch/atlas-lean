# Renaming preserves multi-step beta-eta reduction

Work in the intrinsically typed simply typed lambda calculus over a type of base types, with de Bruijn variables: the terms of type $A$ in a context $\Gamma$ (a list of simple types) are the variables of type $A$, the applications $f\,a$ of a term $f$ of type $D \Rightarrow A$ to a term $a$ of type $D$, both in $\Gamma$, and, when $A = D \Rightarrow E$, the abstractions $\lambda t$ whose body $t$ is a term of type $E$ in $D :: \Gamma$, the context $\Gamma$ extended by a newest variable $0$ of type $D$.

For a term $t$ in $A :: \Gamma$ and a term $a$ of type $A$ in $\Gamma$, the instantiation $t[a]$ substitutes $a$ for the newest variable and replaces each older variable $x+1$ by $x$; for a term $f$ in $\Gamma$, the weakening $f^{\uparrow}$ is $f$ with every variable renamed to its successor. A one-step beta-eta contraction $t \to u$ is a root beta step $(\lambda t)\,a \to t[a]$, a root eta step $\lambda(f^{\uparrow}\,0) \to f$, or such a step inside the function of an application ($f \to g$ gives $f\,a \to g\,a$), inside its argument ($a \to b$ gives $f\,a \to f\,b$), or inside the body of an abstraction ($t \to t'$ gives $\lambda t \to \lambda t'$). Multi-step reduction $\to^*$ is the reflexive-transitive closure of $\to$.

A renaming $\rho$ from $\Gamma$ to $\Delta$ maps every variable of $\Gamma$ to a variable of $\Delta$ of the same type, and $t[\rho]$ renames every free variable of $t$ along $\rho$ (lifting $\rho$ under binders).

For terms $t, u$ of type $A$ in $\Gamma$ with $t \to^* u$ and every renaming $\rho$ from $\Gamma$ to $\Delta$, $t[\rho] \to^* u[\rho]$.
