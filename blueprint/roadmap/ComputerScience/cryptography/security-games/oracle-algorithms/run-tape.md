# Running an oracle algorithm on a randomness tape

Runs an oracle algorithm against the deterministic algorithm `e m r`
(typically encryption), taking the randomness `r` of successive queries from
the tape `ρ`, one entry per query. On output `a`, it continues with `K a n ρ'`
on the unused part `ρ'` of the tape, of length `n`. If the tape runs out, the
result is `d`. Passing the unused tape to a continuation is what two-phase
experiments need.
