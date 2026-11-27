# The embedded Markov chain of the M/G/1 queue

In the M/G/1 queue (Poisson arrivals of rate $\lambda$, i.i.d. service times $B$ independent of the arrivals, one server that works whenever customers are present and serves them one at a time, without interruption, in order of arrival), let $L^d_k$ be the number of customers left behind by the $k$-th departing customer, and $A_{k+1}$ the number of arrivals during the service time of the $(k + 1)$-th customer. Then

$$
L^d_{k+1} = L^d_k - \mathbf 1\{L^d_k > 0\} + A_{k+1},
$$

and since the $A_k$ are i.i.d. and independent of the past, $(L^d_k)_{k \ge 0}$ is a Markov chain on $\{0, 1, 2, \dots\}$, the *embedded* (imbedded) Markov chain at departure epochs. Its transition probabilities are $p_{i,j} = \alpha_{j-i+1}$ for $i > 0$ and $p_{0,j} = \alpha_j$, with $\alpha_m = P(A_1 = m)$ the probability of [$m$ arrivals during a service time](poisson-arrivals-during-an-independent-service-time.md), and $0$ for $j < i - 1$. Looking only at departure epochs removes the elapsed service time from the state, which would otherwise be needed to make the queue length Markov.

## Depends on

- [Poisson arrivals during an independent service time](poisson-arrivals-during-an-independent-service-time.md)

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, Section 7.1 (the two-dimensional state and departure epochs) and Section 7.2 (the recursion for $L^d_{k+1}$, the imbedded Markov chain and its transition matrix, equation (7.2)).
