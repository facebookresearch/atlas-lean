# NbE observational classes of simply typed terms

Fix a type $B$ of base types. Simple types over $B$ are the base types and the arrows $A \Rightarrow C$; a context $\Gamma$ is a list of simple types, $A :: \Gamma$ extends it by a newest variable of type $A$, and $\mathrm{Tm}(\Gamma, A)$ is the type of intrinsically typed de Bruijn terms of type $A$ in $\Gamma$.

Normalization by evaluation sends $t \in \mathrm{Tm}(\Gamma, A)$ to its normal form $\mathrm{nf}(t) \in \mathrm{Nf}(\Gamma, A)$, the type of beta-normal, eta-long normal forms (at an arrow type a lambda over a normal form, at a base type a variable applied to zero or more normal arguments). For $n \in \mathrm{Nf}(\Gamma, A)$, $\lfloor n \rfloor \in \mathrm{Tm}(\Gamma, A)$ is the underlying term, and $\mathrm{nt}(t) = \lfloor \mathrm{nf}(t) \rfloor$ is the normalized term. Terms are NbE-equal, $t \simeq u$, when $\mathrm{nf}(t) = \mathrm{nf}(u)$.

For a type $B$ of base types, a context $\Gamma$ and a simple type $A$, the type $\mathrm{Tm}(\Gamma, A)/{\simeq}$ of NbE classes is the quotient of $\mathrm{Tm}(\Gamma, A)$ by the NbE setoid: terms are identified exactly when their computed normal forms are equal.
