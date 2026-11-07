# Dold realizable sequences

An integer sequence $(a(n))_{n \ge 0}$ is Dold realizable when,
for every integer $n \ge 1$, the Möbius transform $\sum_{d \mid n} \mu(d)\, a(n/d)$ is divisible
by $n$ and non-negative, where $\mu$ is the Möbius function and $d$ runs over the positive
divisors of $n$.

The divisibility condition alone is the classical Dold condition.

## Sources

- the repository's trace-side characterization is `MetaMathlibExt.IsDoldSequence` (Wójcik, Lemma 3). The equivalence between the two forms is not formalized here.
