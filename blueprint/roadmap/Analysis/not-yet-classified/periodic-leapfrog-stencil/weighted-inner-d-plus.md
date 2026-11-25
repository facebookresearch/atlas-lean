# Summation by parts for periodic differences

On the periodic grid $\mathbb{Z}/N\mathbb{Z}$ with spacing $h$, let $(D_+ v)_j = (v_{j+1} - v_j)/h$, $(D_- u)_j = (u_j - u_{j-1})/h$ (indices mod $N$) and $\langle u, v\rangle_h = h \sum_j u_j v_j$. If $N \ge 2$ and $h > 0$, then for all $u, v \in \mathbb{R}^N$
$$\langle D_+ v, u\rangle_h = -\langle v, D_- u\rangle_h.$$
