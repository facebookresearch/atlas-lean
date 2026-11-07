# Overlap alignment score

Given a substitution score $\sigma$ and a gap score $g$, the
overlap score of sequences $s$ and $t$ is the maximum, with floor $0$, of the Needleman–Wunsch
scores of the overlap pairs of $s$ and $t$: the pairs $(s', t')$ where $s'$ is a suffix of $s$
and $t'$ a prefix of $t$, or $s'$ is a prefix of $s$ and $t'$ a suffix of $t$.

The pair of two empty sequences is an overlap pair with score $0$, so the floor never changes
the value: this is the best alignment score of a suffix of one sequence against a prefix of the
other.
