# Hyperharmonic numbers

The hyperharmonic numbers $h_n^{(r)} \in \mathbb{Q}$ of order $r$
and index $n$, for natural numbers $r$ and $n$, are defined by recursion on $r$:
$h_n^{(0)} = 1/n$ for $n \ge 1$, $h_0^{(0)} = 0$, and

$$h_n^{(r+1)} = \sum_{k=1}^{n} h_k^{(r)}.$$

Thus $h_0^{(r)} = 0$ for every order $r$, and $h_n^{(1)} = 1 + 1/2 + \dots + 1/n$ is the $n$-th
harmonic number $H_n$. This is the definition of Conway and Guy.

## Sources

- Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024), Article 24.4.1, Lemma 1 (hyperharmonic numbers `h_n^{(r)}`, after Mező).
