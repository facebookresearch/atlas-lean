# Gittins index theorem

Consider a rested bandit with finitely many arms, each a Markov chain on a finite state space with
bounded rewards: at each time one arm is played, that arm's state moves according to its transition
law and yields a reward, and the other arms stay frozen. With geometric discount factor
$0 < \gamma < 1$, define the Gittins index of arm $i$ in state $x$ as the supremum over positive stopping
times $\tau$ of $\mathbb{E}[\sum_{t < \tau} \gamma^t r_i(x_t)] / \mathbb{E}[\sum_{t < \tau} \gamma^t]$ for the arm
started at $x$. Then a policy that always plays an arm of maximal current index (ties broken
arbitrarily) maximizes the expected total discounted reward. The theorem is stated for rested arms and
geometric discounting; it does not extend in general to restless arms, whose unplayed states also
change.

## Expansion

This node states a precise result. A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Markov chains on a finite state space and stopping times of their natural filtration.
- Statement prerequisite: the rested Markov bandit protocol (only the played arm moves) and its discounted value.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 35.4: the discounted Markov bandit protocol (Figure 35.3), the Gittins index (35.8) and its ratio form (35.9), and Theorem 35.9 (an index policy with ties broken arbitrarily is optimal, under Assumption 35.6, which bounded rewards on a finite state space satisfy). <https://tor-lattimore.com/downloads/book/book.pdf>
