# Uniqueness threshold $p_u$ of bond percolation

Let $G$ be a simple graph on a vertex set $V$. For $p \in [0, 1]$ let $\mathbb{P}_p$ be the Bernoulli($p$) bond law, under which each unordered pair of vertices is independently open with probability $p$, and edges of $G$ are open when their pair is open. The uniqueness threshold of $G$ is

$$p_u(G) = \inf\Big(\{1\} \cup \{p \in [0, 1] : \mathbb{P}_p(\text{there is exactly one infinite open cluster}) = 1\}\Big),$$

so $p_u(G) \in [0, 1]$, and $p_u(G) = 1$ when no such $p$ exists. The event of a unique infinite open cluster need not be measurable for the product structure when $V$ is uncountable, so $\mathbb{P}_p$ is evaluated as an outer measure; when the event is measurable, for example when $V$ is countable, this is its ordinary probability.
