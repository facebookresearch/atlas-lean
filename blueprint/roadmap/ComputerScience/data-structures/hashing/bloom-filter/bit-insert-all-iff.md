# Bits set after inserting a list into a Bloom filter

Let $F$ be a Bloom filter over a type $\alpha$ with $m$ bits, let $L$ be a list of elements of
$\alpha$ and let $i \in \{0, \dots, m - 1\}$. Bit $i$ of the filter obtained by inserting the
elements of $L$ into $F$ is set if and only if bit $i$ of $F$ is set, or $h(x) = i$ for some
element $x$ of $L$ and some hash function $h$ of $F$.
