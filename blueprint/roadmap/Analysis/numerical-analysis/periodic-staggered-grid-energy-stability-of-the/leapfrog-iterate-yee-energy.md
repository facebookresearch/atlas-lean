# The leapfrog iterates conserve the Yee energy

For $N \in \mathbb{N}$, real $h$, $c$, $\Delta t$ and $u, v \in \mathbb{R}^N$, let $(D_+ v)_j = (v_{j+1} - v_j)/h$ (indices mod $N$, $a/0 = 0$). Let one leapfrog step be $v' = v - c\Delta t\, D_+^\top u$, $u' = u + c\Delta t\, D_+ v'$, and let $Q(u, v) = h\sum_j u_j^2 + h\sum_j v_j^2 - h\sum_j u_j\,(c\Delta t\, D_+ v)_j$. If $(u_n, v_n)$ is the pair after $n$ leapfrog steps from $(u_0, v_0)$, then $Q(u_n, v_n) = Q(u_0, v_0)$ for every $n$.
