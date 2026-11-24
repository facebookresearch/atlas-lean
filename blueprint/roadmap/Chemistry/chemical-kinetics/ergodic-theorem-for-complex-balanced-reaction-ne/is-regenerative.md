# Is Regenerative

The process `X` **regenerates at the state `x₀`** at the times `0 ≤ R 0 < R 1 < ⋯`: it is
in `x₀` at each `R k`, the cycle lengths are pairwise independent and identically distributed,
and so are the rewards collected along the cycles by every bounded measurable observable;
the time spent in `x₀` during a cycle has finite mean.

For a continuous-time Markov chain on a countable state space and `R` the successive entrance
times into `x₀`, this is the strong Markov property at the times `R k` (Norris 1997, §3.4 and
Theorem 1.10.1, proof of Theorem 3.8.1): the cycle segments of the path are i.i.d. The time
spent in `x₀` during a cycle is one holding time there, exponential of rate `q(x₀)`.
