# Consensus needs a round

With finitely many processes, at least two of them, and at least two values, no protocol solves consensus in zero rounds, against any number $f$ of crashes and even when no process crashes: each process would decide a function of its own input, validity forces that function to be the identity, and two processes with different inputs then disagree. This is the case $f = 0$ of the $f + 1$ round lower bound.

## Related topics

- [Consensus with $f$ crash failures needs $f + 1$ rounds](f-add-one-le-of-solves.md): the general bound, of which this is the case $f = 0$; its proof repeats this argument when $T = 0$.
