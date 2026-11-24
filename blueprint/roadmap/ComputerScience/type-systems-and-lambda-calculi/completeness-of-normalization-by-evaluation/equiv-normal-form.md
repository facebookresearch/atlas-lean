# NbE classes are in bijection with normal forms

Fix a type $B$ of base types. Simple types over $B$ are the base types and the arrows $A \Rightarrow C$; a context $\Gamma$ is a list of simple types, $A :: \Gamma$ extends it by a newest variable of type $A$, and $\mathrm{Tm}(\Gamma, A)$ is the type of intrinsically typed de Bruijn terms of type $A$ in $\Gamma$.

Normalization by evaluation sends $t \in \mathrm{Tm}(\Gamma, A)$ to its normal form $\mathrm{nf}(t) \in \mathrm{Nf}(\Gamma, A)$, the type of beta-normal, eta-long normal forms (at an arrow type a lambda over a normal form, at a base type a variable applied to zero or more normal arguments). For $n \in \mathrm{Nf}(\Gamma, A)$, $\lfloor n \rfloor \in \mathrm{Tm}(\Gamma, A)$ is the underlying term, and $\mathrm{nt}(t) = \lfloor \mathrm{nf}(t) \rfloor$ is the normalized term. Terms are NbE-equal, $t \simeq u$, when $\mathrm{nf}(t) = \mathrm{nf}(u)$.

Write $\mathrm{Tm}(\Gamma, A)/{\simeq}$ for the quotient of $\mathrm{Tm}(\Gamma, A)$ by the setoid of NbE equality and $\langle t \rangle$ for the class of $t$. The observation of a class is $\mathrm{obs}(\langle t \rangle) = \mathrm{nf}(t)$, and normal forms embed by $\iota(n) = \langle \lfloor n \rfloor \rangle$.

The observation $\mathrm{obs}$ and the embedding $\iota$ are mutually inverse, giving an equivalence between $\mathrm{Tm}(\Gamma, A)/{\simeq}$ and $\mathrm{Nf}(\Gamma, A)$: $\iota(\mathrm{obs}(q)) = q$ for every class $q$ and $\mathrm{obs}(\iota(n)) = n$ for every normal form $n$.
