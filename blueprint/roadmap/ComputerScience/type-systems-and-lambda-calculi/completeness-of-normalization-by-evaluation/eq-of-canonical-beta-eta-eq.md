# Beta-eta convertible canonical terms are equal

Fix a type $B$ of base types. Simple types over $B$ are the base types and the arrows $A \Rightarrow C$; a context $\Gamma$ is a list of simple types, $A :: \Gamma$ extends it by a newest variable of type $A$, and $\mathrm{Tm}(\Gamma, A)$ is the type of intrinsically typed de Bruijn terms of type $A$ in $\Gamma$ (variables of type $A$, applications $f\,a$ with $f \in \mathrm{Tm}(\Gamma, D \Rightarrow A)$ and $a \in \mathrm{Tm}(\Gamma, D)$, and, when $A = D \Rightarrow E$, abstractions $\lambda t$ with body $t \in \mathrm{Tm}(D :: \Gamma, E)$).

For $t \in \mathrm{Tm}(A :: \Gamma, C)$ and $a \in \mathrm{Tm}(\Gamma, A)$, $t[a]$ is $t$ under the single-variable substitution sending the newest variable to $a$ and every older variable $x$ to the variable $x$ of $\Gamma$; $f^{\uparrow}$ is $f$ renamed along the successor map from $\Gamma$ to $A :: \Gamma$, and $0$ is the newest variable.

Beta-eta conversion $t =_{\beta\eta} u$ (between terms of the same type in the same context) is the relation generated inductively by reflexivity, symmetry, transitivity, the congruences ($f =_{\beta\eta} g$ and $a =_{\beta\eta} b$ give $f\,a =_{\beta\eta} g\,b$; $t =_{\beta\eta} t'$ gives $\lambda t =_{\beta\eta} \lambda t'$), the beta axiom $(\lambda t)\,a =_{\beta\eta} t[a]$ and the eta axiom $\lambda(f^{\uparrow}\,0) =_{\beta\eta} f$.

Normalization by evaluation sends $t \in \mathrm{Tm}(\Gamma, A)$ to its normal form $\mathrm{nf}(t) \in \mathrm{Nf}(\Gamma, A)$, the reification at type $A$ of the evaluation of $t$ in the identity semantic environment of $\Gamma$ (each variable reflected as a neutral term). Elements of $\mathrm{Nf}(\Gamma, A)$ are beta-normal, eta-long normal forms: at an arrow type a lambda over a normal form, at a base type a neutral term (a variable applied to zero or more normal arguments). For $n \in \mathrm{Nf}(\Gamma, A)$, $\lfloor n \rfloor \in \mathrm{Tm}(\Gamma, A)$ is the underlying term, and the normalized term of $t$ is $\mathrm{nt}(t) = \lfloor \mathrm{nf}(t) \rfloor$.

A term $c$ is canonical when $c = \lfloor n \rfloor$ for some normal form $n$.

If $t, u \in \mathrm{Tm}(\Gamma, A)$ are both canonical and $t =_{\beta\eta} u$, then $t = u$.
