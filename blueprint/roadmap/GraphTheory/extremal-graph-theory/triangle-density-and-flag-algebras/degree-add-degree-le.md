# Common neighbourhood bound

For all vertices $u$ and $v$ of a finite simple graph on $n$ vertices,

$$\deg u + \deg v \le |N(u) \cap N(v)| + n,$$

because $|N(u)| + |N(v)| = |N(u) \cup N(v)| + |N(u) \cap N(v)|$ and $N(u) \cup N(v)$ has at most $n$ vertices. Summed over the ordered edges $(u, v)$, the left side gives $2\sum_v \deg(v)^2$ and the common neighbourhoods count the [ordered triangles](ordered-triangles.md); this is the first step of [Goodman's bound](goodman-ordered-triangles-nat.md).
