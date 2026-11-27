# The beta-eta setoid on simply typed terms

Fix a type $B$ of base types. Simple types over $B$ are the base types and the arrows $A \Rightarrow C$; a context $\Gamma$ is a list of simple types, $A :: \Gamma$ extends it by a newest variable of type $A$, and $\mathrm{Tm}(\Gamma, A)$ is the type of intrinsically typed de Bruijn terms of type $A$ in $\Gamma$ (variables of type $A$, applications $f\,a$ with $f \in \mathrm{Tm}(\Gamma, D \Rightarrow A)$ and $a \in \mathrm{Tm}(\Gamma, D)$, and, when $A = D \Rightarrow E$, abstractions $\lambda t$ with body $t \in \mathrm{Tm}(D :: \Gamma, E)$).

Beta-eta conversion $t =_{\beta\eta} u$ is the relation generated inductively by reflexivity, symmetry, transitivity, the congruences for application and abstraction, the beta axiom $(\lambda t)\,a =_{\beta\eta} t[a]$ (where $t[a]$ substitutes $a$ for the newest variable and keeps every older variable as a variable of $\Gamma$) and the eta axiom $\lambda(f^{\uparrow}\,0) =_{\beta\eta} f$ (where $f^{\uparrow}$ is $f$ renamed along the successor map and $0$ is the newest variable).

For a type $B$ of base types, a context $\Gamma$ and a simple type $A$, the beta-eta setoid on $\mathrm{Tm}(\Gamma, A)$ is the setoid whose relation is beta-eta conversion $=_{\beta\eta}$, an equivalence relation.
