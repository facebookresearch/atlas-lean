# Term renaming preserves typing

Let $\Gamma$ be a term context with $m$ term variables over $n$ type variables, $t \in \mathrm{Tm}_{n,m}$ a term and $A \in \mathrm{Ty}_n$ a type with $\Gamma \vdash t : A$ ([typing](typing.md)). Let $\Delta$ be a term context with $k$ term variables over the same type variables and $\rho : \{0, \dots, m - 1\} \to \{0, \dots, k - 1\}$ with $\Delta(\rho(i)) = \Gamma(i)$ for every $i$. Then $\Delta \vdash t' : A$, where $t'$ is the [term-variable renaming](../scoped-pure-system-f/rename-2.md) of $t$ by $\rho$.
