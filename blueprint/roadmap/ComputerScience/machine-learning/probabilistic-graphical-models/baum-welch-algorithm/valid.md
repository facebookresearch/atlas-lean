# Valid hidden Markov model parameters

A hidden Markov model with finite state set $S$,
finite observation set $O$ and real initial weights $\pi$, transition weights $a$ and emission
weights $b$ is valid when all its weights are strictly positive and form probability
distributions: $\pi(s) > 0$ for every $s$ and $\sum_{s} \pi(s) = 1$; $a(s, s') > 0$ for all
$s, s'$ and $\sum_{s'} a(s, s') = 1$ for every $s$; and $b(s, o) > 0$ for all $s, o$ and
$\sum_{o} b(s, o) = 1$ for every $s$.
