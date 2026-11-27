# Capture-avoiding substitution

The expression $e[x := v]$ obtained from $e$ by replacing
every free occurrence of the name $x$ by the expression $v$:

- a variable $x$ becomes $v$, and any other variable is unchanged;
- an application is substituted on both sides;
- in $\mathsf{let}\ y = e_1\ \mathsf{in}\ e_2$ the bound expression $e_1$ is always
  substituted, even when $y = x$, since $y$ scopes over the body $e_2$ only;
- under a binder $y$ ($\lambda y$, or $\mathsf{let}\ y$ for its body): if $y = x$ the body is
  unchanged; if $y$ is a free name of $v$, the binder is renamed to a name $z$ outside the names
  of the body and of $v$ and outside $\{x, y\}$, then the body is substituted; otherwise the
  body is substituted with the binder kept.

The binder is renamed only when $y$ is free in $v$, so when no binder of $e$ is free in $v$ the
result is the plain replacement of the free occurrences of $x$.
