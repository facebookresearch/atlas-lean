# A recurrence for Sabar's triangle in small cases

For all natural numbers $n$ and $i$ with
$i < n < 8$, the entries of Sabar's triangle $s$ satisfy
$s(n + 2, i + 1) = s(n, i + 1) + \binom{n+1}{i}$.

This is the source's third basic identity $s(n, i) = s(n-2, i) + \binom{n-1}{i-1}$, stated here
only in these cases. It fails for $i = n$ and $i = n + 1$ (for $i \ge n + 2$ both sides are $0$):
for example $s(2, 1) = 2$ but $s(0, 1) + \binom{1}{0} = 1$.

## Sources

- Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26 (2026), Article A27, Section 2 (identities following from the definition).
