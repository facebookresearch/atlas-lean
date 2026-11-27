# Term-variable renaming in Fω terms

For a map $\rho : \{0, \dots, m-1\} \to \{0, \dots, k-1\}$, the term renaming $t\langle\rho\rangle
\in \mathrm{Tm}_{\Delta,k}$ of $t \in \mathrm{Tm}_{\Delta,m}$ is defined by $x_i\langle\rho\rangle =
x_{\rho(i)}$, $(\lambda A.\,b)\langle\rho\rangle = \lambda A.\,b\langle\rho^{\uparrow}\rangle$,
$(f\,a)\langle\rho\rangle = f\langle\rho\rangle\,a\langle\rho\rangle$, $(\Lambda_\kappa
b)\langle\rho\rangle = \Lambda_\kappa(b\langle\rho\rangle)$ and $(f\,[A])\langle\rho\rangle =
f\langle\rho\rangle\,[A]$, where $\rho^{\uparrow}$ is the [lifted
renaming](../../system-f/scoped-pure-system-f/lift-ren.md) ($0 \mapsto 0$, $i + 1 \mapsto \rho(i) +
1$).
