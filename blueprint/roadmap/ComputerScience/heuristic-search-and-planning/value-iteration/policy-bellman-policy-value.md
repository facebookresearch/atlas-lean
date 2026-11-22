# A policy's value satisfies its Bellman equation

Let $M$ be a Markov decision process
with finitely many states, real rewards $r(s,a)$, and transition probabilities $P(s,a,s')$ that
are nonnegative and sum to $1$ over $s'$, let $0 \le \gamma < 1$, and let $\pi$ be a
deterministic stationary policy with value $V^\pi$. Then $V^\pi$ is a fixed point of the
Bellman operator of $\pi$: for every state $s$,
$V^\pi(s) = r(s,\pi(s)) + \gamma \sum_{s'} P(s,\pi(s),s') \, V^\pi(s')$.
