# Access edges make the root path the downward preferred path

Let $T$ be a tree whose
vertex list is duplicate-free, let $x$ be a vertex of $T$ with root path $p$ (the path from the
root of $T$ down to $x$), and let $E$ be a list of directed edges such that every consecutive
pair of $p$, parent first, lies in $E$, and every edge of $E$ whose first vertex lies on $p$ is
such a consecutive pair. Then the downward preferred path of the preferred-path decomposition of
$T$ under $E$ is $p$.
