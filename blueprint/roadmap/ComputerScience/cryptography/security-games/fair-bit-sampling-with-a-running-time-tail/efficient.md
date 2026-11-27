# Efficient exact sampler on a polynomial input envelope

Fix one machine and one bound
$b$ on auxiliary bit lengths. It halts almost surely on every permitted input. There is one
polynomial $p$ and one nonnegative negligible error $\epsilon$ such that, for every positive
security parameter $n$ and every auxiliary string of length at most $b(n)$, its chance of
running beyond $2p(n)$ steps on the framed pair $(1^n,\mathrm{aux})$ is at most $\epsilon(n)$.
Almost-sure termination is a separate condition, not inferred from this tail inequality.
