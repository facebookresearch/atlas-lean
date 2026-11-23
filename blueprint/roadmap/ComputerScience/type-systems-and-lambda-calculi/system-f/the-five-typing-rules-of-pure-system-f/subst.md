# Term substitution preserves typing

Let $\Gamma$ be a term context with $m$ term variables over $n$ type variables, $t \in \mathrm{Tm}_{n,m}$ a term and $A \in \mathrm{Ty}_n$ a type with $\Gamma \vdash t : A$ ([typing](typing.md)). Let $\Delta$ be a term context with $k$ term variables over the same type variables and $\sigma$ a term substitution with $\Delta \vdash \sigma(i) : \Gamma(i)$ for every $i < m$. Then $\Delta \vdash t[\sigma] : A$ ([simultaneous substitution](../scoped-pure-system-f/subst-2.md)).
