# Forward-backward smoothing is a joint-to-likelihood ratio

Let $g$ be a hidden Markov model
with finite state set $S$ and weights in a semifield, and let $x_0, x_1, \dots$ be observations.
For all $t, k \in \mathbb{N}$ and $s \in S$, the smoothing weight
$\alpha_t(s)\, \beta_k(t, s) / L_{t+k}$, where $\alpha$ and $\beta$ are the forward and backward
variables and $L_{t+k}$ is the likelihood of $x_0, \dots, x_{t+k}$, equals the joint weight of
$x_0, \dots, x_{t+k}$ and the state $s$ at time $t$, divided by $L_{t+k}$.

When the weights are probabilities and the likelihood is positive, this ratio is the conditional
state marginal.
