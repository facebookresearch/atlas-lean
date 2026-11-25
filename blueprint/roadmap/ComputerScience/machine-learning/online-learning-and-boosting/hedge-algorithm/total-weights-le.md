# Weight decay over a Hedge run

Let $n > 0$ and let $\eta$ be a real number. For every
sequence of rounds with losses in $[0, 1]$ and all positive initial weights $w$ on $n$ experts,
the total weight after running Hedge with learning rate $\eta$ from $w$ is at most
$W \exp(-(1 - e^{-\eta}) L)$, where $W$ is the total weight of $w$ and $L$ is the algorithm's
total loss over the rounds for the run from $w$ with learning rate $\eta$.
