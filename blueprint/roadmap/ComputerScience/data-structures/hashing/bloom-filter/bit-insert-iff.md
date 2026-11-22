# Bits set by an insertion

Let $F$ be a Bloom filter over $\alpha$ with $m$ bits, let
$x \in \alpha$ and let $i \in \{0, \dots, m - 1\}$. Bit $i$ of the filter obtained by inserting
$x$ into $F$ is set if and only if bit $i$ of $F$ is set or some hash function $h$ of $F$
satisfies $h(x) = i$.
