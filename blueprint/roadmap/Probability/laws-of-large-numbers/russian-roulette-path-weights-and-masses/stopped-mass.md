# Stopped mass after exactly n transitions

For a finite set of states $S$, stop probabilities $q$, a survival kernel $Q$, a start state $i$ and $n \in \mathbb{N}$, the stopped mass at level $n$ is the total completed-path weight $\sum q(x_n) \prod_{k<n} Q(x_k, x_{k+1})$ over all paths $(x_0, \dots, x_n)$ with $x_0 = i$, that is, over paths with exactly $n$ transitions. It is a raw weight.
