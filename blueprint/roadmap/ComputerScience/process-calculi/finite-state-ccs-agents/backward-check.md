# Backward certificate check

Let $s$ list the labelled transitions $(a, x')$ of each
implementation code $x$, let $t$ list those of each specification code $y$, and let $R$ be a
finite list of code pairs. The backward check succeeds when for every pair $(x, y)$ in $R$ and
every entry $(a, y')$ of $t(y)$, at least one of the following holds: $a = \tau$ and
$(x, y')$ is in $R$; some entry $(a, x')$ of $s(x)$ with the same label has $(x', y')$ in $R$;
or some entry $(\tau, x'')$ of $s(x)$ has $(x'', y)$ in $R$, and the first occurrence of
$(x'', y)$ in $R$ comes strictly before the first occurrence of $(x, y)$.
