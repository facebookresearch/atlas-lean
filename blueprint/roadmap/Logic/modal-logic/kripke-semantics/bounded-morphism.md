# Bounded morphism

Let $M$ and $N$ be Kripke models over the same atoms, with sets of worlds
$W$ and $V$ and accessibility relations $R_M$ and $R_N$. A bounded morphism from $M$ to $N$ is
a map $f : W \to V$ such that every atom holds at a world $w$ in $M$ if and only if it holds
at $f(w)$ in $N$; whenever $w \mathrel{R_M} w'$, also $f(w) \mathrel{R_N} f(w')$ (forth); and
whenever $f(w) \mathrel{R_N} v'$, there is a world $w'$ with $w \mathrel{R_M} w'$ and
$f(w') = v'$ (back).

Bounded morphisms are also called p-morphisms.
