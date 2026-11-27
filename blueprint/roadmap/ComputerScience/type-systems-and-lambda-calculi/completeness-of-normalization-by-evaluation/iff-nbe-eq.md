# Beta-eta conversion is NbE equivalence

Fix a type $B$ of base types. Simple types over $B$ are base types and arrows $A \Rightarrow A'$. A context $\Gamma$ is a list of types; a variable of type $A$ in $\Gamma$ is a de Bruijn index into $\Gamma$ (index $0$ is the head of the list, the innermost binder), and $A :: \Gamma$ is $\Gamma$ extended by a new innermost variable $x_0$ of type $A$. Terms of type $A$ in $\Gamma$ are intrinsically typed: variables of type $A$, applications $f\,a$ of a term $f$ of type $D \Rightarrow A$ to a term $a$ of type $D$, both in $\Gamma$, and, when $A = D \Rightarrow E$, abstractions $\lambda t$ whose body $t$ has type $E$ in $D :: \Gamma$. A renaming $\rho : \Gamma \to \Delta$ sends each variable of $\Gamma$ to a variable of $\Delta$ of the same type, and a substitution $\sigma : \Gamma \to \Delta$ sends each variable of $\Gamma$ of type $A$ to a term of type $A$ in $\Delta$; $t[\rho]$ and $t[\sigma]$ denote their actions on a term $t$. For renamings $\rho : \Gamma \to \Delta$ and $\sigma : \Delta \to \Theta$, $\sigma \circ \rho : \Gamma \to \Theta$ is the renaming $\rho$ followed by $\sigma$, which sends each variable $x$ to $\sigma(\rho(x))$.

A normal form of type $A$ in $\Gamma$ is a beta-normal, eta-long term: at an arrow type a lambda whose body is a normal form, at a base type a neutral term (a variable applied to zero or more normal arguments); $\lceil n \rceil$ is the term underlying a normal form $n$, and $n[\rho]$ renames its free variables. Normalization by evaluation sends a term $t$ of type $A$ in $\Gamma$ to the normal form $\mathrm{nf}(t)$ obtained by evaluating $t$ in the identity semantic environment of $\Gamma$ (each variable interpreted as its reflection) and reifying the result at type $A$; the normalized term is $\mathrm{norm}(t) = \lceil \mathrm{nf}(t) \rceil$.

Terms $t, u$ of type $A$ in $\Gamma$ are NbE-equivalent, $t \equiv_{\mathrm{nbe}} u$, when $\mathrm{nf}(t) = \mathrm{nf}(u)$.

Beta-eta conversion $t =_{\beta\eta} u$, between terms of the same type in the same context, is the least relation that is reflexive, symmetric and transitive, is closed under application (from $f =_{\beta\eta} g$ and $a =_{\beta\eta} b$ infer $f\,a =_{\beta\eta} g\,b$) and abstraction (from $t =_{\beta\eta} t'$ infer $\lambda t =_{\beta\eta} \lambda t'$), and contains beta, $(\lambda t)\,a =_{\beta\eta} t[a]$, and eta, $\lambda\,(f^{\uparrow}\,x_0) =_{\beta\eta} f$. Here the instantiation $t[a]$ substitutes $a$ for the innermost variable of $t$ and sends every other variable to the corresponding variable of the outer context, and $f^{\uparrow}$ is $f$ renamed past the new innermost variable $x_0$.

For terms $t, u$ of type $A$ in $\Gamma$,

$$t =_{\beta\eta} u \iff t \equiv_{\mathrm{nbe}} u,$$

that is, two terms are beta-eta convertible exactly when normalization by evaluation computes the same normal form for both.
