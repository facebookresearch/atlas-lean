# Forward certificate check

Let $s$ list the labelled transitions $(a, x')$ of each
implementation code $x$, let $t$ list those of each specification code $y$, and let $R$ be a
finite list of code pairs. The forward check succeeds when for every pair $(x, y)$ in $R$ and
every entry $(a, x')$ of $s(x)$, either $a = \tau$ and $(x', y)$ is in $R$, or some entry
$(a, y')$ of $t(y)$ with the same label has $(x', y')$ in $R$.
