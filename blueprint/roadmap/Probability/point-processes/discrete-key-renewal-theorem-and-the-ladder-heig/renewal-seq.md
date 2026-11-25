# Renewal Seq

The **renewal sequence** of an interarrival law `f : ℕ → ℝ` (only `f 1, f 2, …` are
used): `u 0 = 1` and `u (n + 1) = ∑_{k = 0}^{n} f (k + 1) * u (n - k)`. When `f` is the law
of a strictly positive integer waiting time, `u n` is the probability that some renewal
epoch equals `n`.
