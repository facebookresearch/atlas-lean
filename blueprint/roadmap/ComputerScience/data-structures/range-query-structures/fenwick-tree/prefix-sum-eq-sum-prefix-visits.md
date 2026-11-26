# The Fenwick prefix query sums the visited entries

Let $t$ represent a list $a$ over
an additive commutative monoid. For every natural requested length $k$, the installed prefix
query of $t$ is the sum of the stored entries at the endpoints in the prefix visit list for
length $t.\mathrm{size}=|a|$. The visit list uses only stored positions from $1$ to
$\min(k,|a|)$, so the dummy entry and out-of-bounds defaults do not contribute.
