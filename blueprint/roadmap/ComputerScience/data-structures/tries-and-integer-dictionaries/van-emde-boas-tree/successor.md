# Successor query in a two-level van Emde Boas tree

Let $T$ be a two-level van Emde Boas
tree over the universe $\{0, \dots, m^2 - 1\}$ and let $x = hm + \ell$ with $0 \le h, \ell < m$, so
that $x$ sits at position $\ell$ of cluster $h$. If cluster $h$ has a set position after $\ell$, the
successor of $x$ in $T$ is $hm + \ell'$ for the least such position $\ell'$. Otherwise, let $h'$ be
the least cluster index with $h < h'$ whose summary bit is set; the successor is $h'm + \ell''$ for
the least position $\ell''$ set in cluster $h'$. If there is no such $h'$, or cluster $h'$ has no
set position, $x$ has no successor.

In a valid tree, the successor of $x$ is the least member of $T$ greater than $x$.
