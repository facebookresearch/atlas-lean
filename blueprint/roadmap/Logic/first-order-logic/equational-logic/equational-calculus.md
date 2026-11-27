# Equational calculus

Let $E$ be a set of equations over $T_\Sigma(X)$. The relation $E \vdash s \approx t$ (the equation $s \approx t$ is *derivable* from $E$) is the least relation closed under the rules

- **Reflexivity:** $E \vdash t \approx t$ for every term $t$;
- **Symmetry:** from $E \vdash t \approx t'$ derive $E \vdash t' \approx t$;
- **Transitivity:** from $E \vdash t \approx t'$ and $E \vdash t' \approx t''$ derive $E \vdash t \approx t''$;
- **Congruence:** from $E \vdash t_1 \approx t'_1, \dots, E \vdash t_n \approx t'_n$ derive $E \vdash f(t_1, \dots, t_n) \approx f(t'_1, \dots, t'_n)$ for every function symbol $f$ of arity $n$;
- **Instance:** $E \vdash t\sigma \approx t'\sigma$ for every equation $(t \approx t') \in E$ and every substitution $\sigma$.

## Depends on

- [Equational consequence and E-algebras](equational-consequence-and-e-algebras.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.2, the inference system for equational consequences, p. 107.
