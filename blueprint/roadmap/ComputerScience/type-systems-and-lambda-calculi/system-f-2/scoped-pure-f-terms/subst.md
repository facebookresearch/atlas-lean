# Simultaneous term substitution in Fω

For a term substitution $\sigma$ assigning to each $i < m$ a [term](tm.md) $\sigma(i) \in
\mathrm{Tm}_{\Delta,k}$, the substitution $t[\sigma] \in \mathrm{Tm}_{\Delta,k}$ of $t \in
\mathrm{Tm}_{\Delta,m}$ is defined by $x_i[\sigma] = \sigma(i)$, $(\lambda A.\,b)[\sigma] = \lambda
A.\,b[\sigma^{\uparrow}]$ (with the [lifted substitution](lift-sub.md)), $(f\,a)[\sigma] =
f[\sigma]\,a[\sigma]$, $(\Lambda_\kappa b)[\sigma] = \Lambda_\kappa(b[\sigma'])$ where $\sigma'(i)$
is $\sigma(i)$ with its type variables [renamed](ty-rename.md) by the successor renaming $\alpha_j
\mapsto \alpha_{j+1}$, and $(f\,[A])[\sigma] = f[\sigma]\,[A]$.
