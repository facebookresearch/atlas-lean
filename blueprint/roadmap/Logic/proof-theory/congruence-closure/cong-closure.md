# Cong Closure

Let $E$ be a binary relation on ground terms (a set of ground equalities). The congruence closure $\equiv_E$ of $E$ is the smallest relation on ground terms closed under the rules:

- if $E(t, s)$ then $t \equiv_E s$;
- $t \equiv_E t$ for every term $t$;
- if $t \equiv_E s$ then $s \equiv_E t$;
- if $t \equiv_E s$ and $s \equiv_E u$ then $t \equiv_E u$;
- if $t_1 \equiv_E t_2$ and $s_1 \equiv_E s_2$ then $\mathrm{app}(t_1, s_1) \equiv_E \mathrm{app}(t_2, s_2)$.

Thus it is the least congruence containing $E$.
