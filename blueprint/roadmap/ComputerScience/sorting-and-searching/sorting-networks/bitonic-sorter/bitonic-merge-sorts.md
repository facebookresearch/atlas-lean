# The bitonic merger sorts every bitonic `0`-`1` input

Let $k, b \in \mathbb{N}$ and let $f$
assign a Boolean value to each wire $x \in \mathbb{N}$, with Booleans ordered by
$\mathrm{false} < \mathrm{true}$. If the sequence $f(b), f(b + 1), \dots, f(b + 2^k - 1)$ is
bitonic, then running the bitonic merger on the block $[b, b + 2^k)$ on $f$ gives an assignment
$g$ that is sorted on that block: $g(b + i) \le g(b + j)$ whenever $i \le j < 2^k$.

This is the correctness of CLRS's `BITONIC-SORTER`, proved by recursion on the half-cleaner
lemma.
