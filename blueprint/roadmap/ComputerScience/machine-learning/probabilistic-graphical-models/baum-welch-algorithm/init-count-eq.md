# The expected starts from forward-backward

Let $h$ be a valid hidden Markov model with
finite state set $S$ and finite observation set $O$, let $T \in \mathbb{N}$, and let
$x_0, \dots, x_{N-1}$ be observation sequences. For a sequence $x_n$ write $\alpha^n_0(s)$ for its
forward variable at time $0$ and state $s$, $\beta^n_{T,0}(s)$ for its backward variable from
time $0$ with $T$ remaining steps (the weight of the observations $x_n(1), \dots, x_n(T)$ given the
state $s$ at time $0$), and $L_n$ for the likelihood of $x_n(0), \dots, x_n(T)$. Then for every
state $s$, the expected number of sequences whose state path of length $T + 1$ starts in $s$,
under the posterior of $h$, is $\sum_{n < N} \alpha^n_0(s)\, \beta^n_{T,0}(s) / L_n$.
