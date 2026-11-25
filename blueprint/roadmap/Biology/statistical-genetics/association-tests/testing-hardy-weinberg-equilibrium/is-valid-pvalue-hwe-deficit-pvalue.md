# The exact heterozygote-deficit test is valid in finite samples

For all natural numbers $N$ and $n_A \le 2N$, under the
[uniform placement model](uniform-arrangements.md) $U_{N, n_A}$, the uniform law on the sets of
$n_A$ of the $2N$ gamete slots (a probability measure), the
[exact p-value for a heterozygote deficit](hwe-deficit-pvalue.md) of the observed
[number of heterozygotes](../../../../Probability/hypothesis-testing/exact-test-for-hardy-weinberg-equilibrium/het-count.md)
is a
[valid p-value](../../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md):
the sets of slots with p-value at most $t$ have probability at most $t$, for every $t \in [0, 1]$.
Without the condition $n_A \le 2N$ the model is the zero measure and the statement holds only
vacuously (Wigginton, Cutler and Abecasis 2005).
