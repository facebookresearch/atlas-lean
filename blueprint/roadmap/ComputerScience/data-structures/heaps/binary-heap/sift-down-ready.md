# Sift-down precondition

For an array $a$ over a type ordered by $\le$, write
$p(j) = \lfloor (j-1)/2 \rfloor$ for the parent of index $j$. The array $a$ is ready for
sift-down at index $i$ when $i$ is a valid index of $a$; $a_{p(j)} \le a_j$ for every valid index
$j > 0$ with $p(j) \ne i$; and, if $i > 0$, $a_{p(i)} \le a_j$ for every valid index $j > 0$ with
$p(j) = i$.

Thus the only edges that may violate heap order are those leaving $i$, and moving either child
of $i$ up to position $i$ keeps the edge entering $i$ ordered.
