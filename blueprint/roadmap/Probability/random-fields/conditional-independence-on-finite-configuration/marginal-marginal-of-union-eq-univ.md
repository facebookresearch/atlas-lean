# Marginalizing in two steps, no variable summed twice

Let $V$ and $\alpha$ be finite
types, let $p$ be a real-valued weight on the configurations $x : V \to \alpha$, let
$U, W \subseteq V$ with $U \cup W = V$, and let $p_W$ be the $W$-marginal of $p$, the weight
sending $x$ to the total weight of the configurations that agree with $x$ on $W$. Then for every
configuration $x$, the $U$-marginal of $p_W$ at $x$ equals the $(U \cap W)$-marginal of $p$ at
$x$. When instead $U \subseteq W$, the two-step marginal picks up a counting factor
(`marginal_marginal`).
