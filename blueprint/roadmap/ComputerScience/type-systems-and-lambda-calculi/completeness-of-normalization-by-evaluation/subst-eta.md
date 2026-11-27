# The eta law on beta-eta classes survives substitution

Fix a type $B$ of base types. Simple types over $B$ are the base types and the arrows $A \Rightarrow C$; a context $\Gamma$ is a list of simple types, $A :: \Gamma$ extends it by a newest variable of type $A$, and $\mathrm{Tm}(\Gamma, A)$ is the type of intrinsically typed de Bruijn terms of type $A$ in $\Gamma$ (variables of type $A$, applications $f\,a$ with $f \in \mathrm{Tm}(\Gamma, D \Rightarrow A)$ and $a \in \mathrm{Tm}(\Gamma, D)$, and, when $A = D \Rightarrow E$, abstractions $\lambda t$ with body $t \in \mathrm{Tm}(D :: \Gamma, E)$).

Beta-eta conversion $t =_{\beta\eta} u$ is the relation generated inductively by reflexivity, symmetry, transitivity, the congruences for application and abstraction, the beta axiom $(\lambda t)\,a =_{\beta\eta} t[a]$ (where $t[a]$ substitutes $a$ for the newest variable and keeps every older variable as a variable of $\Gamma$) and the eta axiom $\lambda(f^{\uparrow}\,0) =_{\beta\eta} f$ (where $f^{\uparrow}$ is $f$ renamed along the successor map and $0$ is the newest variable).

Write $\mathrm{Tm}(\Gamma, A)/{=_{\beta\eta}}$ for the quotient of $\mathrm{Tm}(\Gamma, A)$ by the setoid of beta-eta conversion, and $[t]$ for the class of a term $t$.

A renaming $\rho$ from $\Gamma$ to $\Delta$ sends each variable of $\Gamma$ to a variable of the same type in $\Delta$, and $t\langle\rho\rangle$ renames the free variables of $t$; on classes, $\rho \cdot [t] = [t\langle\rho\rangle]$.

A substitution $\sigma$ from $\Gamma$ to $\Delta$ sends each variable of $\Gamma$ to a term of the same type in $\Delta$, and $t[\sigma]$ is simultaneous substitution; on classes, $\sigma \cdot [t] = [t[\sigma]]$.

On classes, $\mathrm{app}([f], [a]) = [f\,a]$ and $\mathrm{lam}([t]) = [\lambda t]$.

Here $\mathrm{succ}$ is the successor renaming from $\Gamma$ to $A :: \Gamma$ and $[0]$ is the class of the newest variable of $A :: \Gamma$.

For a substitution $\sigma$ from $\Gamma$ to $\Delta$ and a class $f \in \mathrm{Tm}(\Gamma, A \Rightarrow C)/{=_{\beta\eta}}$, $\sigma \cdot \mathrm{lam}(\mathrm{app}(\mathrm{succ} \cdot f, [0])) = \sigma \cdot f$.
