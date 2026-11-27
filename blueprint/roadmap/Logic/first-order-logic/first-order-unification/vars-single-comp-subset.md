# The elimination step of unification introduces no variables

Write $V(F)$ for the set
of variables of a list $F$ of equations. Let $x_0$ be a variable, $t$ a term in which $x_0$ does
not occur, $e = (e_1, e_2)$ an equation such that every variable of $t$ occurs in $e_1$ or $e_2$,
and $E$ a list of equations, and let $E'$ be obtained from $E$ by substituting $t$ for $x_0$ on
both sides of every equation. Let $s_0$ be a substitution such that, for every variable $x$,
every variable of $s_0(x)$ is $x$ or lies in $V(E')$, and let $\sigma$ be the substitution that
applies first the replacement of $x_0$ by $t$ and then $s_0$. Then for every variable $x$, every
variable of $\sigma(x)$ is $x$, occurs in $e_1$ or $e_2$, or lies in $V(E)$.
