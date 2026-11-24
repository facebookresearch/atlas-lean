# Second-price payment

Let $I$ be a finite set of at least two agents and $w$ a winner rule, mapping every bid vector
$t \in \mathbb{R}^I$ to an agent $w(t)$. In the second-price auction the winner pays the highest competing
bid and the others pay nothing: the payment of agent $i$ at the bids $t$ is $\max_{j \neq i} t_j$ if
$w(t) = i$, and $0$ otherwise (Nisan 2007, Definition 9.12).

## Sources

- N. Nisan, "Introduction to mechanism design (for computer scientists)", Chapter 9 of N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, Definition 9.12.
