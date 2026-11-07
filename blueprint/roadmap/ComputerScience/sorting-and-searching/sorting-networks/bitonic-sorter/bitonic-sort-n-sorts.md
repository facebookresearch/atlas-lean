# The bitonic sorter sorts every `0`-`1` input

Let $k, b \in \mathbb{N}$ and let $f$ assign
a Boolean value to each wire $x \in \mathbb{N}$, with Booleans ordered by
$\mathrm{false} < \mathrm{true}$. Running Batcher's bitonic sorter on the block $[b, b + 2^k)$
on $f$ gives an assignment $g$ that is sorted on that block: $g(b + i) \le g(b + j)$ whenever
$i \le j < 2^k$.
