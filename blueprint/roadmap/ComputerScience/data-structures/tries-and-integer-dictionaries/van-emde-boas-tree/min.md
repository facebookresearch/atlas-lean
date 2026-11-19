# Minimum query of a van Emde Boas tree

Let $t$ be a two-level van Emde Boas tree over the
universe $\{0, \dots, m^2 - 1\}$. If some summary bit of $t$ is set, let $h$ be the least cluster
index whose summary bit is set; if cluster $h$ has a set position, let $\ell$ be the least one.
The minimum query on $t$ then returns the element $h \cdot m + \ell$. If no summary bit is set,
or cluster $h$ has no set position, it returns no element.

In a valid tree this is the least stored element.
