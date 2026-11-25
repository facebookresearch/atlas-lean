# One-step graph minor

For finite graphs $H$ and $G$, $H$ arises from $G$ by one minor step
when one of the following holds. Isomorphism: $H$ is isomorphic to $G$. Vertex deletion: for some
vertex $a$ of $G$ there is an injective map $f$ from the vertices of $H$ to the vertices of $G$
whose image consists of all vertices other than $a$, such that vertices $u, v$ of $H$ are adjacent
exactly when $f(u), f(v)$ are adjacent in $G$. Edge deletion: for some edge $xy$ of $G$ there is a
bijection $e$ from the vertices of $H$ to the vertices of $G$ such that, for all vertices $u, v$ of
$H$, the vertices $e(u), e(v)$ are adjacent in $G$ whenever $u, v$ are adjacent in $H$, and if
$e(u), e(v)$ are adjacent in $G$, then either $u, v$ are adjacent in $H$ or the pair $(e(u), e(v))$
is $(x, y)$ or $(y, x)$; moreover, $e^{-1}(x), e^{-1}(y)$ are not adjacent in $H$. Edge
contraction: for some edge $ab$ of $G$ there is a surjective map $f$ from the vertices of $G$ to
the vertices of $H$ with $f(a) = f(b)$ such that, for all vertices $x, y$ of $G$, $f(x) = f(y)$
implies $x = y$ or $(x, y)$ is $(a, b)$ or $(b, a)$, and vertices $u, v$ of $H$ are adjacent
exactly when $u \ne v$ and there are adjacent vertices $u', v'$ of $G$ with $f(u') = u$ and
$f(v') = v$.

Stable source: https://en.wikipedia.org/wiki/Robertson%E2%80%93Seymour_theorem.
