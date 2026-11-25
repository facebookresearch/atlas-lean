# Expected run ends per read tend to $e^{-a}$ under sparsity

For every $N$, let $N$ reads have start positions on a circular genome of $G_N$ positions, with
windows $V_N$ such that $V_N + 1 \le G_N$, and let $E_N$ be the sum over the positions of the
[normalized counts](normalized-count.md) of the start tuples in which the position is a
[run end](ends-run.md) for the window $V_N$ (the
[expected number of run ends](expected-ends-run.md) for independent uniform starts). If
$N V_N / G_N \to a$ for a real number $a$ and $N / G_N \to 0$, then

$$\frac{E_N}{N} \to e^{-a} \quad (N \to \infty).$$

For example, if $V_N = W_N = L_N - T_N$ with $W_N / L_N \to \sigma$ and $N L_N / G_N \to c$, then
$a = c\sigma$, which corresponds to Lander and Waterman's $N e^{-c\sigma}$ apparent islands.
