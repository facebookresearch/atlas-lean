# Local views determine states

Let $P$ be an oral-message protocol for the generals $G$
with states $\sigma$ and messages $M$. Let $N$ be a type of nodes, node $k$ running the code of
the general $\rho(k) \in G$, and let $L$ be a property of nodes. For each round $r$ and node
$k$, let $s_r(k), s'_r(k) \in \sigma$ be two states and $\mu_r(k), \mu'_r(k) : G \to M$ two
families of received messages. Suppose that for every $r$ and every node $k$ satisfying $L$,
$s_{r+1}(k)$ is the state to which general $\rho(k)$ of $P$ moves in round $r$ from $s_r(k)$ on
the messages $\mu_r(k)$, and $s'_{r+1}(k)$ the one to which it moves from $s'_r(k)$ on
$\mu'_r(k)$; that $s_0(k) = s'_0(k)$ for every $k$ satisfying $L$; and that for every $r$, if
$s_r(k) = s'_r(k)$ for all $k$ satisfying $L$, then $\mu_r(k) = \mu'_r(k)$ for all $k$
satisfying $L$. Then $s_r(k) = s'_r(k)$ for every $r$ and every $k$ satisfying $L$.
