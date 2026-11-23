# APPROX-VERTEX-COVER is at most twice any vertex cover

Let $G$ be a simple graph and $L$ a
list of ordered pairs of vertices such that $u$ and $v$ are adjacent in $G$ for every $(u, v)$ in
$L$. Then for every vertex cover $S$ of $G$, finite or infinite, the cover $C$ that
APPROX-VERTEX-COVER returns on $L$ satisfies $|C| \le 2|S|$, with sizes in
$\mathbb{N} \cup \{\infty\}$.
