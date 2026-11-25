# The expected transitions from forward-backward

Let $h$ be a valid hidden Markov model
with finite state set $S$, finite observation set $O$, transition weights $a$ and emission
weights $b$, let $T \in \mathbb{N}$, and let $x_0, \dots, x_{N-1}$ be observation sequences. For a
sequence $x_n$ write $\alpha^n_t(s)$ for its forward variable at time $t$ and state $s$,
$\beta^n_{k,t}(s)$ for its backward variable (the weight of the observations
$x_n(t + 1), \dots, x_n(t + k)$ given the state $s$ at time $t$), and $L_n$ for the likelihood of
$x_n(0), \dots, x_n(T)$. Then for all states $s, s'$, the expected number of transitions
$s \to s'$ along state paths of length $T + 1$, summed over the sequences under the posterior of
$h$, is
$\sum_{n < N} \sum_{t < T} \alpha^n_t(s)\, a(s, s')\, b(s', x_n(t + 1))\,
\beta^n_{T - t - 1, t + 1}(s') / L_n$.

Each summand is Rabiner's $\xi_t(s, s')$ for the sequence $x_n$.
