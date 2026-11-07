# Euler recurrence for the Josephus function

For all natural numbers $k \ge 2$ and
$n \ge 1$, the Josephus function $J_k$ for elimination step $k$ satisfies
$J_k(n+1) = ((J_k(n) + k - 1) \bmod (n+1)) + 1$.

## Sources

- concept `jis_sem_e1c9a353312d2a1564410d6e`; source statements `jis_1986849a138b5f4709dd284a`, `jis_2b78f59babf40128fececb65`, `jis_597f2ddde7f055cc80cc8489`, `jis_cddd7a6b10023809e13a6c78`, `jis_fe4f24c64ecfdad23577e877`; clause `euler_recurrence`. The hypotheses `_hk` and `_hn` record the source domain `k ≥ 2`, `n ≥ 1` and are unused by the proof.
