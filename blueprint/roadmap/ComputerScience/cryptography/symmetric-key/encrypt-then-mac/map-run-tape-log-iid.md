# Eager sampling with transcripts

If an oracle computation makes at most $n$ queries, then for every $m$, running it with a transcript
on a random tape of $n + m$ independent samples of $\rho$ gives the same distribution of output and
transcript as its logged run against the oracle that answers $x$ with $h(x, r)$ for a fresh sample
$r$ of $\rho$.
