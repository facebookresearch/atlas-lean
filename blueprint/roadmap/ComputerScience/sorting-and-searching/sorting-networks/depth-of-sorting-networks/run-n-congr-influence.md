# Outputs depend only on the influence set

Let $f_0, g_0 : \mathbb{N} \to \alpha$ be two
inputs with values in a linear order $\alpha$, let $S$ assign to each wire $x$ a finite set $S(x)$
of input positions, and let $F, G : \mathbb{N} \to \alpha$ be wire values such that for every wire
$x$, if $f_0$ and $g_0$ agree on $S(x)$, then $F(x) = G(x)$. Then for every list of comparators
and every wire $x$, if $f_0$ and $g_0$ agree on the influence set of $x$ obtained from $S$ through
the comparators, running the comparators on $F$ and on $G$ gives the same value at wire $x$.
