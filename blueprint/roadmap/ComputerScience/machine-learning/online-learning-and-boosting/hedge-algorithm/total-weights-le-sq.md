# Weight decay over a Hedge run, second-order form

Let $n > 0$ and $\eta \ge 0$. For every
sequence of rounds with nonnegative losses and all positive initial weights $w$ on $n$ experts,
the total weight after running Hedge with learning rate $\eta$ from $w$ is at most
$W \exp(-\eta L + \eta^2 Q)$. Here $W$ is the total weight of $w$, $L$ is the algorithm's total
loss over the rounds and $Q$ is the sum of the rounds' weighted second moments, both for the run
from $w$ with learning rate $\eta$.
