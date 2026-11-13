# Extracting the minimum of a d-ary heap lowers its multiplicity by one

Let $h$ be a
$d$-ary min-heap over a linearly ordered type. If extracting the minimum from $h$ succeeds,
returning a value $x$ and a heap $h'$, then the multiplicity of $x$ in the multiset of elements
of $h'$ is its multiplicity in the multiset of elements of $h$ minus one.
