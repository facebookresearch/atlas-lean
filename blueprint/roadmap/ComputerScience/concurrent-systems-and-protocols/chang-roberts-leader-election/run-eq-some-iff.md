# Runs are multistep transitions

Given a natural-number identifier $\mathrm{id}(k)$ for
each process $k$ of the ring, for all global states $s, t$ and every list $\kappa$ of processes,
running the schedule $\kappa$ from $s$ returns $t$ if and only if the Chang–Roberts transition
system with identifiers $\mathrm{id}$ has a multistep transition from $s$ to $t$ labelled by
$\kappa$.
