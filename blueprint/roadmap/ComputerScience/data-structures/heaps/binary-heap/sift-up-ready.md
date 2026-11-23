# Arrays ready for sift-up

Let $a$ be an array of length $|a|$ over a type with a relation
$\le$, indexed from $0$, and for $j > 0$ let $p(j) = \lfloor (j - 1)/2 \rfloor$ be the parent of
$j$. The array $a$ is ready for sift-up at an index $i$ when $i < |a|$, when $a_{p(j)} \le a_j$ for
every $j \ne i$ with $0 < j < |a|$, and when, if $i > 0$, also $a_{p(i)} \le a_j$ for every $j$
with $0 < j < |a|$ and $p(j) = i$.
