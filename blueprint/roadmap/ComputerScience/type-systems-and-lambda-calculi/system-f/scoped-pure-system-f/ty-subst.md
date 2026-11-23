# Type substitution in System F terms

For a type substitution $\sigma$ from $n$ to $k$ type variables, the type substitution $t[\sigma]$ of a [term](tm.md) $t \in \mathrm{Tm}_{n,m}$ is the term of $\mathrm{Tm}_{k,m}$ that applies the [type substitution](subst.md) $\sigma$ to every type annotation and type argument: $x_i[\sigma] = x_i$, $(\lambda A.\,b)[\sigma] = \lambda A[\sigma].\,b[\sigma]$, $(f\,a)[\sigma] = f[\sigma]\,a[\sigma]$, $(\Lambda b)[\sigma] = \Lambda\,(b[\sigma^{\uparrow}])$ with the [lifted substitution](lift-sub.md), and $(f\,[A])[\sigma] = f[\sigma]\,[A[\sigma]]$.
