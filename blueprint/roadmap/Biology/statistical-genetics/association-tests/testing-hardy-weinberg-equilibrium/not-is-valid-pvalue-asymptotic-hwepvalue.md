# The asymptotic HWE test is anti-conservative for sparse counts

In the sparse null model, with $N = 10$ individuals carrying $n_A = 2$ copies of $A$ under the
[uniform placement model](uniform-arrangements.md) $U_{10, 2}$ (the heterozygote count is then $0$
with probability $1/19$ and $2$ with probability $18/19$), the
[asymptotic p-value](asymptotic-hwepvalue.md) of the observed heterozygote count is not a
[valid p-value](../../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md):
the asymptotic test at level $0.05$ rejects with probability at least $1/19 > 0.05$, since the count
$0$ has asymptotic p-value at most $0.05$. The
[exact p-value is valid](is-valid-pvalue-hwe-exact-pvalue.md) in the same model (Emigh 1980;
Wigginton, Cutler and Abecasis 2005).
