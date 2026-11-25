# Lemma 3, occupied recurrence

Let $k \ge 1$, let $p_1 < p_2 < \cdots$ be the primes in
increasing order, and let $r_1, \dots, r_{k+1}$ be natural numbers. For $m \in \{k, k + 1\}$
write $P_m = p_1 \cdots p_m$, let $\gamma_m(n)$ be the number of $i \le m$ with
$n \equiv r_i \pmod{p_i}$, let $\mathrm{occ}(m)$ be the number of integers $n$ with
$1 \le n \le P_m$ and $\gamma_m(n) > 1$, and let $\mathrm{free}(m)$ be the number of those with
$\gamma_m(n) = 0$. Then
$\mathrm{occ}(k+1) + \mathrm{free}(k) = P_k + (p_{k+1} - 1) \cdot \mathrm{occ}(k)$.

In the paper's form this reads
$\mathrm{occ}(k+1) = P_k + (p_{k+1} - 1) \cdot \mathrm{occ}(k) - \mathrm{free}(k)$.

## Sources

- Florian Pausinger, "Counting Appearances of Integers in Sets of Arithmetic Progressions", Lemma 3.
