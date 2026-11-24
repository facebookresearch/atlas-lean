# The canonical map from beta-eta classes commutes with renaming

Fix a type $B$ of base types. Simple types over $B$ are the base types and the arrows $A \Rightarrow C$; a context $\Gamma$ is a list of simple types, $A :: \Gamma$ extends it by a newest variable of type $A$, and $\mathrm{Tm}(\Gamma, A)$ is the type of intrinsically typed de Bruijn terms of type $A$ in $\Gamma$.

Normalization by evaluation sends $t \in \mathrm{Tm}(\Gamma, A)$ to its normal form $\mathrm{nf}(t) \in \mathrm{Nf}(\Gamma, A)$, the type of beta-normal, eta-long normal forms (at an arrow type a lambda over a normal form, at a base type a variable applied to zero or more normal arguments). For $n \in \mathrm{Nf}(\Gamma, A)$, $\lfloor n \rfloor \in \mathrm{Tm}(\Gamma, A)$ is the underlying term, and $\mathrm{nt}(t) = \lfloor \mathrm{nf}(t) \rfloor$ is the normalized term. Terms are NbE-equal, $t \simeq u$, when $\mathrm{nf}(t) = \mathrm{nf}(u)$.

Write $\mathrm{Tm}(\Gamma, A)/{\simeq}$ for the quotient of $\mathrm{Tm}(\Gamma, A)$ by the setoid of NbE equality and $\langle t \rangle$ for the class of $t$. The observation of a class is $\mathrm{obs}(\langle t \rangle) = \mathrm{nf}(t)$, and normal forms embed by $\iota(n) = \langle \lfloor n \rfloor \rangle$.

Beta-eta conversion $t =_{\beta\eta} u$ is the relation generated inductively by reflexivity, symmetry, transitivity, the congruences for application and abstraction, the beta axiom $(\lambda t)\,a =_{\beta\eta} t[a]$ and the eta axiom $\lambda(f^{\uparrow}\,0) =_{\beta\eta} f$. Write $[t]$ for the class of $t$ in the quotient $\mathrm{Tm}(\Gamma, A)/{=_{\beta\eta}}$ by beta-eta conversion, with observation $\mathrm{obs}_{\beta\eta}([t]) = \mathrm{nf}(t)$.

The canonical map $\kappa : \mathrm{Tm}(\Gamma, A)/{=_{\beta\eta}} \to \mathrm{Tm}(\Gamma, A)/{\simeq}$ sends $[t]$ to $\langle t \rangle$; it is well defined because beta-eta convertible terms have the same normal form.

A renaming $\rho$ from $\Gamma$ to $\Delta$ sends each variable of $\Gamma$ to a variable of the same type in $\Delta$; $t\langle\rho\rangle$ and $n\langle\rho\rangle$ rename the free variables of a term or a normal form, and on classes $\rho \cdot \langle t \rangle = \langle t\langle\rho\rangle \rangle$.

Renaming acts on beta-eta classes by $\rho \cdot [t] = [t\langle\rho\rangle]$. For a renaming $\rho$ from $\Gamma$ to $\Delta$ and a beta-eta class $q$ in $\mathrm{Tm}(\Gamma, A)/{=_{\beta\eta}}$, $\kappa(\rho \cdot q) = \rho \cdot \kappa(q)$.
