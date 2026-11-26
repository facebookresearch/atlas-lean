# Lipschitz increments give a stable one-step method

Let $E$ be a real normed space and $\Phi(t, x, h)$ the increment function of a one-step method $x_{j+1} = x_j + h_j\, \Phi(t_j, x_j, h_j)$. Suppose that for some $L \ge 0$, $x \mapsto \Phi(s, x, h)$ is $L$-Lipschitz for every $s \in [t_0, T]$ and step $h \in (0, T - t_0]$. Then the method is stable on $[t_0, T]$: there is a constant $S$ such that on every grid from $t_0$ to $T$, every perturbed sequence $z_{j+1} = z_j + h_j \Phi(t_j, z_j, h_j) + \delta_{j+1}$ satisfies $\|x_j - z_j\| \le S\big(\|x_0 - z_0\| + \sum_k \|\delta_k\|\big)$.
