# Pairwise forward-backward

Let $h$ be a hidden Markov model with finite state set $S$,
transition weights $a$ and emission weights $b$ in a semiring, and let $x$ be an observation
sequence. For all $t, k \in \mathbb{N}$ and states $s, s'$, the joint weight of the observations
$x(0), \dots, x(t + 1 + k)$ and the transition $s \to s'$ from time $t$ to time $t + 1$ equals
$\alpha_t(s)\, a(s, s')\, b(s', x(t + 1))\, \beta_{k, t + 1}(s')$, where $\alpha_t(s)$ is the
forward variable and $\beta_{k, t + 1}(s')$ is the backward variable, the weight of the
observations $x(t + 2), \dots, x(t + 1 + k)$ given the state $s'$ at time $t + 1$.
