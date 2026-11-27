# A mild solution starts at its initial value

Let $S$ be a strongly continuous semigroup on a real Banach space $X$, $F : X \to X$, $x_0 \in X$ and $T \ge 0$. A mild solution on $[0, T]$ of $u' = A u + F(u)$, $u(0) = x_0$ (with $A$ the generator of $S$) is a $u : \mathbb{R} \to X$ continuous on $[0, T]$ such that, for every $t \in [0, T]$, $s \mapsto S(t - s) F(u(s))$ is integrable on $[0, t]$ and $u(t) = S(t) x_0 + \int_0^t S(t - s) F(u(s))\, ds$. Every mild solution satisfies $u(0) = x_0$.
