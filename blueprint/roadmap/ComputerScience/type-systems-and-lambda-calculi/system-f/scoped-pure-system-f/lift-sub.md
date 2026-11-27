# Lifting a type substitution under a type binder

For a type substitution $\sigma$ assigning to each $i < n$ a [type](ty.md) $\sigma(i) \in \mathrm{Ty}_k$, its lifting $\sigma^{\uparrow}$ assigns $\alpha_0$ to $0$ and, to $i + 1$, the type $\sigma(i)$ [renamed](rename.md) by $j \mapsto j + 1$; it is a substitution from $n + 1$ to $k + 1$ type variables.
