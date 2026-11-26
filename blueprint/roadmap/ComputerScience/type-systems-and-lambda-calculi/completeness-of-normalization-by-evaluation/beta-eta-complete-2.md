# Completeness of beta-eta conversion for NbE equality

Fix a type $B$ of base types. Simple types over $B$ are the base types and the arrows $A \Rightarrow C$; a context $\Gamma$ is a list of simple types, $A :: \Gamma$ extends it by a newest variable of type $A$, and $\mathrm{Tm}(\Gamma, A)$ is the type of intrinsically typed de Bruijn terms of type $A$ in $\Gamma$.

Normalization by evaluation sends $t \in \mathrm{Tm}(\Gamma, A)$ to its normal form $\mathrm{nf}(t) \in \mathrm{Nf}(\Gamma, A)$, the type of beta-normal, eta-long normal forms (at an arrow type a lambda over a normal form, at a base type a variable applied to zero or more normal arguments). For $n \in \mathrm{Nf}(\Gamma, A)$, $\lfloor n \rfloor \in \mathrm{Tm}(\Gamma, A)$ is the underlying term, and $\mathrm{nt}(t) = \lfloor \mathrm{nf}(t) \rfloor$ is the normalized term. Terms are NbE-equal, $t \simeq u$, when $\mathrm{nf}(t) = \mathrm{nf}(u)$.

Beta-eta conversion $t =_{\beta\eta} u$ is the relation generated inductively by reflexivity, symmetry, transitivity, the congruences for application and abstraction, the beta axiom $(\lambda t)\,a =_{\beta\eta} t[a]$ and the eta axiom $\lambda(f^{\uparrow}\,0) =_{\beta\eta} f$. Write $[t]$ for the class of $t$ in the quotient $\mathrm{Tm}(\Gamma, A)/{=_{\beta\eta}}$ by beta-eta conversion, with observation $\mathrm{obs}_{\beta\eta}([t]) = \mathrm{nf}(t)$.

For a type $B$ of base types, a context $\Gamma$ and a simple type $A$, beta-eta conversion is complete at $\Gamma$ and $A$ when every two terms $t, u \in \mathrm{Tm}(\Gamma, A)$ with $\mathrm{nf}(t) = \mathrm{nf}(u)$ satisfy $t =_{\beta\eta} u$. This is the converse of the fact that convertible terms have equal normal forms.
