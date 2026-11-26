# Values below their Bellman image lie below the policy value

Let $M$ be a Markov decision
process with a finite set of states $S$, real rewards and stochastic transition probabilities,
and let $0 \le \gamma < 1$. Let $\pi$ be a deterministic policy, with Bellman operator $T^\pi$ and
value $V^\pi$. If $V : S \to \mathbb{R}$ satisfies $V(s) \le (T^\pi V)(s)$ for every state $s$,
then $V(s) \le V^\pi(s)$ for every state $s$.
