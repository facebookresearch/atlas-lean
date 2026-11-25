# Scott's extension extends a continuous map

If $f : X \to P(\omega)$ is continuous on the subspace $X$ of $Y$, then Scott's extension $\bar f$ agrees with $f$ on $X$ (D. Scott, *Data types as lattices*, SIAM J. Comput. 5(3) (1976), Theorem 1.5). Scott's proof: $\bar f(x) \subseteq f(x)$ because every open $U \ni x$ contains $x$ itself. Conversely, if $m \in f(x)$, then $f^{-1}\{z \mid m \in z\}$ is open in $X$, so it is $X \cap U$ for an open $U \ni x$, and that $U$ witnesses $m \in \bar f(x)$.

## Informally uses

- [The sets of naturals containing `n` are Scott-open](is-open-set-of-mem.md): the open set $\{z \mid m \in z\}$.

## Sources

- D. Scott, *Data types as lattices*, SIAM Journal on Computing 5(3) (1976), 522–587, doi:10.1137/0205037.
