# Instantiating a term binder preserves typing

Let $\Gamma$ be a term context with $m$ term variables over $n$ type variables, $A, B \in \mathrm{Ty}_n$, $b \in \mathrm{Tm}_{n,m+1}$ and $a \in \mathrm{Tm}_{n,m}$. If $A \cdot \Gamma \vdash b : B$ and $\Gamma \vdash a : A$ ([typing](typing.md)), then $\Gamma \vdash b[a] : B$ ([instantiation](../scoped-pure-system-f/instantiate-2.md)).
