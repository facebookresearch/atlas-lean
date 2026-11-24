# Probe Bound

Open addressing under uniform hashing: a counting bound on probe prefixes.
Slots are `Fin m`, and `S` is the set of occupied slots, of size `n = S.card`.
A probe sequence is a permutation `π` of the slots (`π i` is the `i`-th probed
slot).

For `k ≤ m`, the permutations whose first `k` probes all land in `S` number
exactly `n (n - 1) ⋯ (n - k + 1) * (m - k)!`: the falling factorial `(n)_k` times
the orderings of the remaining `m - k` slots. When `S` is a proper subset of the
slots, an unsuccessful search stops at the first free slot, so these are exactly
the probe sequences on which it makes more than `k` probes. For `k > m`, every
slot is among the first `k` probes, so the count is `m!` when `S` is the whole
table and `0` otherwise; a full table has no free slot.

The theorem states the real-valued upper bound `m! * (n / m) ^ k` on this count,
for every `k`.
