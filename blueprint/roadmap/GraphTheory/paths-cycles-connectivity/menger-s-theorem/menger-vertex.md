# Menger's theorem, vertex form

Let $G$ be a simple graph on a finite vertex set and let
$s$ and $t$ be distinct, nonadjacent vertices of $G$. Then there is a natural number $n$ with
the following two properties. First, there is a set $C$ of exactly $n$ vertices with
$s \notin C$ and $t \notin C$ such that every walk from $s$ to $t$ passes through a vertex of
$C$, and every set of vertices with these three properties has at least $n$ elements. Second,
there are $n$ paths $P_1, \dots, P_n$ from $s$ to $t$ (walks that repeat no vertex) such that
every vertex lying on both $P_i$ and $P_j$ for some $i \ne j$ is $s$ or $t$, and every finite
family of paths from $s$ to $t$ with this property has at most $n$ members. Thus the minimum
number of vertices other than $s$ and $t$ whose removal separates $s$ from $t$ equals the
maximum number of pairwise internally disjoint paths from $s$ to $t$.

## Sources

- K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927), 96–115, doi:10.4064/fm-10-1-96-115; statement as in https://en.wikipedia.org/wiki/Menger%27s_theorem (`menger-s1`).
