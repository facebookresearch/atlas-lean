# Van der Waerden's theorem

For all positive integers $r$ and $k$ there is a natural
number $N$ such that for every coloring of $\{1, \dots, N\}$ with $r$ colors there are natural
numbers $a \ge 1$ and $d \ge 1$ with $a + (k - 1)d \le N$ such that each of the $k$ terms
$a, a + d, \dots, a + (k - 1)d$ has the same color as $a$.

Proof: apply the Hales–Jewett theorem to the digit-sum encoding $x \mapsto 1 + \sum_i x_i$
of words over the alphabet $\{0, \dots, k - 1\}$, so that a combinatorial line becomes an
arithmetic progression. This follows the standard derivation in Graham, Rothschild, and
Spencer, *Ramsey Theory*, Section 2.3, from van der Waerden (1927).

## Sources

- https://en.wikipedia.org/wiki/Van_der_Waerden%27s_theorem
