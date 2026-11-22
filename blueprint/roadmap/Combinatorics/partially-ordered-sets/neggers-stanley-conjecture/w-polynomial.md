# The $W$-polynomial of a labeled poset

Let $R$ be a relation on the labels
$\{0, 1, \dots, n-1\}$, with $R(i, j)$ read as $i \lt _P j$ in the poset $P$ it generates. A linear
extension of $P$ is a permutation $w$ of the labels such that $a < b$ whenever $R(w(a), w(b))$,
that is, a word $w(0)\,w(1) \cdots w(n-1)$ listing every label once with $w(a)$ before $w(b)$
whenever $R(w(a), w(b))$. The $W$-polynomial is the integer polynomial
$W(P, x) = \sum_w x^{d(w)}$, summed over the linear extensions $w$ of $P$, where $d(w)$ is the
number of descents of $w$.

Linear extensions of $R$ and of its transitive closure coincide, so $R$ need not be transitive.
