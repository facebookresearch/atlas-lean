# A root beta step inside a typed context is one beta-eta contraction

Work in the intrinsically typed simply typed lambda calculus over a type of base types, with de Bruijn variables: the terms of type $A$ in a context $\Gamma$ (a list of simple types) are the variables of type $A$, the applications $f\,a$ of a term $f$ of type $D \Rightarrow A$ to a term $a$ of type $D$, both in $\Gamma$, and, when $A = D \Rightarrow E$, the abstractions $\lambda t$ whose body $t$ is a term of type $E$ in $D :: \Gamma$, the context $\Gamma$ extended by a newest variable $0$ of type $D$.

For a term $t$ in $A :: \Gamma$ and a term $a$ of type $A$ in $\Gamma$, the instantiation $t[a]$ substitutes $a$ for the newest variable and replaces each older variable $x+1$ by $x$; for a term $f$ in $\Gamma$, the weakening $f^{\uparrow}$ is $f$ with every variable renamed to its successor. A one-step beta-eta contraction $t \to u$ is a root beta step $(\lambda t)\,a \to t[a]$, a root eta step $\lambda(f^{\uparrow}\,0) \to f$, or such a step inside the function of an application ($f \to g$ gives $f\,a \to g\,a$), inside its argument ($a \to b$ gives $f\,a \to f\,b$), or inside the body of an abstraction ($t \to t'$ gives $\lambda t \to \lambda t'$).

A typed one-hole context $C$ has a hole of type $B$ in context $\Gamma$ and produces a term of type $C'$ in context $\Delta$; it is the hole, $C\,a$, $f\,C$ or $\lambda C$, and $C[t]$ plugs a term $t$ into the hole with no renaming, so abstractions above the hole may bind free variables of $t$.

For every context $C$ whose hole has type $B$ in $\Gamma$, every term $t$ of type $B$ in $A :: \Gamma$ and every term $a$ of type $A$ in $\Gamma$, $C[(\lambda t)\,a] \to C[t[a]]$.
