# A proposal

Fix, for each proposer, a ranking of the $n$ receivers and, for each receiver,
a ranking of the $n$ proposers (rank $0$ is the first choice). Let $s$ be a state of deferred
acceptance in which proposer $m$ has made $k$ proposals. If $k < n$, then $m$ proposes to the
receiver $w$ of rank $k$ in his ranking: his number of proposals becomes $k + 1$, and $w$ now
holds $m$ if she held nobody or ranks $m$ strictly above the proposer she held, and keeps her old
holder otherwise; all other counts and holders are unchanged. If $k \ge n$, the state is
unchanged.
