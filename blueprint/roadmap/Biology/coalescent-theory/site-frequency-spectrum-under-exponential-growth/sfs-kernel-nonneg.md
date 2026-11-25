# The Griffiths–Tavaré kernel is nonnegative

For all natural numbers `n`, `i` and `k`, the
[Griffiths–Tavaré kernel](../site-frequency-spectrum-under-variable-populatio/sfs-kernel.md)
satisfies

`g_{n,i,k} = k C(n - i - 1, k - 2) / C(n - 1, k - 1) ≥ 0`,

where the subtractions are truncated at `0` and division by `0` gives `0`. The kernel is
intended for `1 ≤ i ≤ n - 1` and `2 ≤ k ≤ n`, where no subtraction is truncated and
`C(n - 1, k - 1) > 0`; the inequality holds at every index, with these conventions outside that
range.
