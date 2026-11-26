# Policy iteration

Let $M$ be a Markov decision process with a finite set of states $S$, a
finite nonempty set of actions $A$, real rewards and stochastic transition probabilities, and let
$0 \le \gamma < 1$. Policy iteration run for $n$ steps from a deterministic policy $\pi : S \to A$
is the policy obtained from $\pi$ by applying the policy improvement step $n$ times.
