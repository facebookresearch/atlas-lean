# The adjoint of the forward difference is unique

On the periodic grid $\mathbb{Z}/N$ with spacing $h$, let $(D_+ v)_j = (v_{j+1} - v_j)/h$. Let $N \ge 2$, $h > 0$ and $(D_- u)_j = (u_j - u_{j-1})/h$. If an operator $T$ satisfies $\langle D_+ v, u \rangle_h = \langle v, T u \rangle_h$ for all $u, v$, with $\langle u, v \rangle_h = h \sum_j u_j v_j$, then $T = -D_-$.
