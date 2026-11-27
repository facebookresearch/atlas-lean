# Interpreting an abstraction of beta-eta classes

Fix a type $B$ of base types. Simple types over $B$ are the base types and the arrows $A \Rightarrow C$; a context $\Gamma$ is a list of simple types, $A :: \Gamma$ extends it by a newest variable of type $A$, and $\mathrm{Tm}(\Gamma, A)$ is the type of intrinsically typed de Bruijn terms of type $A$ in $\Gamma$ (variables of type $A$, applications $f\,a$ with $f \in \mathrm{Tm}(\Gamma, D \Rightarrow A)$ and $a \in \mathrm{Tm}(\Gamma, D)$, and, when $A = D \Rightarrow E$, abstractions $\lambda t$ with body $t \in \mathrm{Tm}(D :: \Gamma, E)$).

Beta-eta conversion $t =_{\beta\eta} u$ is the relation generated inductively by reflexivity, symmetry, transitivity, the congruences for application and abstraction, the beta axiom $(\lambda t)\,a =_{\beta\eta} t[a]$ (where $t[a]$ substitutes $a$ for the newest variable and keeps every older variable as a variable of $\Gamma$) and the eta axiom $\lambda(f^{\uparrow}\,0) =_{\beta\eta} f$ (where $f^{\uparrow}$ is $f$ renamed along the successor map and $0$ is the newest variable).

Write $\mathrm{Tm}(\Gamma, A)/{=_{\beta\eta}}$ for the quotient of $\mathrm{Tm}(\Gamma, A)$ by the setoid of beta-eta conversion, and $[t]$ for the class of a term $t$.

Given an interpretation $I$ assigning a type $I(b)$, in an arbitrary universe, to each base type $b$: $[\![A]\!]$ is $I(b)$ at a base type and the function type $[\![A]\!] \to [\![C]\!]$ at $A \Rightarrow C$; an environment $\eta$ for $\Gamma$ assigns to each variable of type $C$ an element of $[\![C]\!]$, and $v \cdot \eta$ extends it by $v$ for a newest variable; $[\![t]\!]\eta$ is $\eta(x)$ for a variable, $[\![f]\!]\eta\,([\![a]\!]\eta)$ for $f\,a$, and $v \mapsto [\![t]\!](v \cdot \eta)$ for $\lambda t$. The interpretation of a class is $[\![\,[t]\,]\!]\eta = [\![t]\!]\eta$, well defined because beta-eta conversion is sound in every such model.

On classes, $\mathrm{app}([f], [a]) = [f\,a]$ and $\mathrm{lam}([t]) = [\lambda t]$.

For an interpretation $I$, an environment $\eta$ for $\Gamma$ and a class $b \in \mathrm{Tm}(A :: \Gamma, C)/{=_{\beta\eta}}$, $[\![\mathrm{lam}(b)]\!]\eta$ is the function $v \mapsto [\![b]\!](v \cdot \eta)$ on $[\![A]\!]$.
