# Predecessor query in a two-level van Emde Boas tree

Let $T$ be a two-level van Emde Boas
tree over the universe $\{0, \dots, m^2 - 1\}$ and let $x = hm + \ell$ with $0 \le h, \ell < m$, so
that $x$ sits at position $\ell$ of cluster $h$. If cluster $h$ has a set position before $\ell$,
the predecessor of $x$ in $T$ is $hm + \ell'$ for the greatest such position $\ell'$. Otherwise,
let $h'$ be the greatest cluster index with $h' < h$ whose summary bit is set; the predecessor is
$h'm + \ell''$ for the greatest position $\ell''$ set in cluster $h'$. If there is no such $h'$, or
cluster $h'$ has no set position, $x$ has no predecessor.

In a valid tree, the predecessor of $x$ is the greatest member of $T$ less than $x$.
