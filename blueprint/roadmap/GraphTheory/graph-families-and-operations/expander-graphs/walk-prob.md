# Probability of an event for a random walk on a regular graph

For a $d$-regular graph $G$ with $d > 0$ on a nonempty vertex set $V$ of size $N$, with adjacency matrix $A$, a length $t$ and a property $P$ of vertex sequences $(V_0, \dots, V_t)$, the probability that the random walk satisfies $P$ is

$$\Pr[P] = \sum_{w \text{ satisfying } P} \frac{1}{N} \prod_{i < t} \frac{A(w_i, w_{i+1})}{d},$$

the sum running over the sequences $w = (w_0, \dots, w_t) \in V^{t+1}$: $V_0$ is uniform and each $V_{i+1}$ is a uniformly random neighbour of $V_i$ (S. Vadhan, *Pseudorandomness* (2012), Section 4.2, random walks $V_1, \dots, V_t$ from a uniform start vertex, indexed here from $0$).
