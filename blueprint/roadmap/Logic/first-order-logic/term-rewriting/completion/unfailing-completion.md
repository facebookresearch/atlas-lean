# Unfailing completion

Let $\succ$ be a [reduction ordering](../reduction-ordering.md) that is total on ground terms. For a set $E$ of equations, $s \to_{E_\succ} t$ holds if there are an equation $u \approx v$ or $v \approx u$ in $E$, a position $p$ of $s$ and a substitution $\sigma$ with $s|_p = u\sigma$, $t = s[v\sigma]_p$ and $u\sigma \succ v\sigma$; this relation terminates. $E$ is *ground convergent* with respect to $\succ$ if for all ground terms $s, t$ with $s \leftrightarrow_E^* t$ there is a ground term $v$ with $s \to_{E_\succ}^* v \leftarrow_{E_\succ}^* t$ (likewise for $E \cup R$).

Let $u_1 \doteq v_1$ and $u_2 \doteq v_2$ be equations of $E$ renamed apart, $p$ a position of $u_1$ with $u_1|_p$ not a variable, $\sigma$ a most general unifier of $u_1|_p$ and $u_2$, and suppose $u_i\sigma \not\preceq v_i\sigma$ for $i = 1, 2$. Then $\langle v_1\sigma, (u_1\sigma)[v_2\sigma]_p \rangle$ is a *semi-critical pair* of $E$; $\mathrm{SP}_\succ(E)$ is the set of them, and semi-critical pairs of $E \cup R$ are defined in the same way. Overlaps of an equation with itself at the root must be included.

*Unfailing completion* uses the rules of [Knuth–Bendix completion](knuth-bendix-completion.md) with Deduce replaced by: $E, R \vdash E \cup \{s \approx t\}, R$ if $\langle s, t \rangle \in \mathrm{SP}_\succ(E \cup R)$. A run is *fair* if $\mathrm{SP}_\succ(E_* \cup R_*) \subseteq E_\infty$.

## Depends on

- [Knuth–Bendix completion](knuth-bendix-completion.md)
- [Reduction ordering](../reduction-ordering.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.7, pp. 127–128 (Bachmair, Dershowitz and Plaisted): the relation $\to_{E_\succ}$, ground convergence, semi-critical pairs, the modified Deduce rule and fairness.
