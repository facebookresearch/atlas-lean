# The expected emissions from forward-backward

Let $h$ be a valid hidden Markov model with
finite state set $S$ and finite observation set $O$, let $T \in \mathbb{N}$, and let
$x_0, \dots, x_{N-1}$ be observation sequences. For a sequence $x_n$ write $\alpha^n_t(s)$ for its
forward variable at time $t$ and state $s$, $\beta^n_{k,t}(s)$ for its backward variable (the
weight of the observations $x_n(t + 1), \dots, x_n(t + k)$ given the state $s$ at time $t$), and
$L_n$ for the likelihood of $x_n(0), \dots, x_n(T)$. Then for every state $s$ and observation $o$,
the expected number of emissions of $o$ from $s$ along state paths of length $T + 1$, summed over
the sequences under the posterior of $h$, is
$\sum_{n < N} \sum_{t \le T,\ x_n(t) = o} \alpha^n_t(s)\, \beta^n_{T - t, t}(s) / L_n$.
