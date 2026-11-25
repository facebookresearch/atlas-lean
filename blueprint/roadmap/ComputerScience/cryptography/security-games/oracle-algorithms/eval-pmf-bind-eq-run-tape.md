# Eager sampling with a continuation

Let the randomness space `Rnd` be finite and nonempty, and let the
continuations satisfy: whenever `cont a n` holds, sampling a uniform tape of
length `n` and running `K' a n` on it has the distribution `K a`. For an
oracle algorithm `c` that makes at most `q` queries and ends in an output `a`
with `cont a n` for the remaining budget `n`, running `c` against the
randomized oracle `m ↦ e m r` with fresh uniform `r` per query and then `K`
gives the same distribution as drawing a uniform tape of length `q` up front
and running `c` and then `K'` on it.
