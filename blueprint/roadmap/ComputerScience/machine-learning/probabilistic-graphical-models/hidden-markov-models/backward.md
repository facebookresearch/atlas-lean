# Backward variables of a hidden Markov model

Let $h$ be a hidden Markov model with finite
state set $S$, transition weights $a$ and emission weights $b$ in a semiring $R$, and let
$x_0, x_1, \dots$ be observations. The backward variables $\beta_k(t, s) \in R$, for
$k, t \in \mathbb{N}$ and $s \in S$, are defined by $\beta_0(t, s) = 1$ and

$$\beta_{k+1}(t, s) = \sum_{s' \in S} a(s, s')\, b(s', x_{t+1})\, \beta_k(t + 1, s').$$

Thus $\beta_k(t, s)$ is the weight of the observations $x_{t+1}, \dots, x_{t+k}$ given the state
$s$ at time $t$.
