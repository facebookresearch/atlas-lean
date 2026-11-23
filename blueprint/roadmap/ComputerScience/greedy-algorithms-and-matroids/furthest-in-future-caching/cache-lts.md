# Legal cache transitions

For a capacity $k \in \mathbb{N}$, this is the labelled
transition system whose states are lists of blocks (the cache contents, in any order) and whose
labels are cache events. Write $|C|$ for the length of a list $C$, $x :: C$ for $C$ with $x$
prepended, and $C \setminus v$ for $C$ with the first occurrence of $v$ removed. There is a
transition from $C$ to $C'$ labelled by a hit on $r$ when $r \in C$ and $C'$ is a permutation of
$C$; labelled by a miss on $r$ with no eviction when $r \notin C$ and either $k = 0$ and $C$ and
$C'$ are both empty, or $|C| < k$ and $C'$ is a permutation of $r :: C$; and labelled by a miss on
$r$ evicting $v$ when $k > 0$, $r \notin C$, $|C| = k$, $v \in C$ and $C'$ is a permutation of
$r :: (C \setminus v)$.
