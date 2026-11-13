# Standard translation

For $n$ variables $x_0, \dots, x_{n-1}$ in scope and a term $t$
of the modal language for the current world, the standard translation $ST_t(\varphi)$ of a
modal formula $\varphi$ is the first-order formula over the modal language in these variables
defined by recursion on $\varphi$: $ST_t(a) = P_a(t)$ for an atom $a$; $ST_t(\bot) = \bot$;
$ST_t(\varphi \to \psi) = ST_t(\varphi) \to ST_t(\psi)$; and
$ST_t(\Box \varphi) = \forall x_n \, (R(t, x_n) \to ST_{x_n}(\varphi))$, where $x_n$ is a fresh
variable and $ST_{x_n}(\varphi)$ is taken with $n + 1$ variables in scope.
