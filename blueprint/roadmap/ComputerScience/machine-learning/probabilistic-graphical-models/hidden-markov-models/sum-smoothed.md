# Smoothed weights sum to one

For a hidden Markov model with a finite set of states $S$ and
weights in a semifield, observations $x_0, x_1, \dots$ and times $t, k \in \mathbb{N}$, if the
likelihood $L_{t+k}$ of $x_0, \dots, x_{t+k}$ is nonzero, then the smoothed weights
$\gamma_{t,k}(s) = \alpha_t(s)\,\beta_{k,t}(s) / L_{t+k}$, with $\alpha$ the forward and $\beta$
the backward variables, sum to $1$ over all states $s \in S$.
