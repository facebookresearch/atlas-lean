# The likelihood from the forward and backward variables

Let $h$ be a hidden Markov model
with finite state set $S$ and weights in a semiring, and let $x_0, x_1, \dots$ be observations.
Write $\alpha_t(s)$ for the forward variable (the weight of $x_0, \dots, x_t$ with the state at
time $t$ equal to $s$) and $\beta_k(t, s)$ for the backward variable. Then for all
$t, k \in \mathbb{N}$, the likelihood of $x_0, \dots, x_{t+k}$ equals

$$\sum_{s \in S} \alpha_t(s)\, \beta_k(t, s).$$
