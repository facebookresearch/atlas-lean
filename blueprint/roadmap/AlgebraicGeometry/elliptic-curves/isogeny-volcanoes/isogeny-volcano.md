# Isogeny volcano

Let $\ell$ be a prime. An $\ell$-isogeny volcano consists of a finite
vertex set $V$, a multigraph on $V$ with edge multiplicities $m(v, w)$, a depth $d \in \mathbb{N}$,
a surjective level map $\mathrm{lev} : V \to \{0, 1, \dots, d\}$ and a surface degree
$s \in \mathbb{N}$ with $s \le 2$, subject to the following conditions, where the surface is the
set of vertices of level $0$. Every surface vertex $v$ satisfies
$\sum_{w \in V,\ \mathrm{lev}(w) = 0} m(v, w) = s$. Every vertex $v$ of positive level has a
unique parent: $\sum_{w \in V,\ \mathrm{lev}(w) + 1 = \mathrm{lev}(v)} m(v, w) = 1$. Whenever
$m(v, w) > 0$, either $v$ and $w$ both lie on the surface or their levels differ by exactly one.
Every vertex $v$ with $\mathrm{lev}(v) < d$ has degree $\sum_{w \in V} m(v, w) = \ell + 1$, where a
loop at $v$ contributes its multiplicity once. Finally, the multigraph is connected: any two
vertices are joined by a path along which consecutive vertices have positive edge multiplicity.
