# A policy's Bellman update is at most the optimal one

Let $M$ be a Markov decision
process with a finite set of states $S$, a finite nonempty set of actions $A$, and rewards
$r(s,a)$ and transition probabilities $P(s,a,s')$ in a field $K$ with a linear order, let
$\gamma \in K$, and let $\pi : S \to A$ be a deterministic stationary policy. For every
$V : S \to K$ and every state $s$, the Bellman operator of $\pi$ applied to $V$ is at most the
Bellman optimality operator applied to $V$ at $s$:
$r(s,\pi(s)) + \gamma \sum_{s'} P(s,\pi(s),s') \, V(s') \le
\max_a \bigl(r(s,a) + \gamma \sum_{s'} P(s,a,s') \, V(s')\bigr)$.
