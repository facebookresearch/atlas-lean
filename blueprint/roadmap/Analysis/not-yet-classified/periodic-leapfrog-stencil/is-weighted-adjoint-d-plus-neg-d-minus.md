# Backward difference is the weighted adjoint of the forward difference

On the periodic grid $\mathbb{Z}/N\mathbb{Z}$ with spacing $h$, let $(D_+ v)_j = (v_{j+1} - v_j)/h$ and $(D_- u)_j = (u_j - u_{j-1})/h$ (indices mod $N$), and let $\langle u, v\rangle_h = h \sum_{j} u_j v_j$. An operator $T$ is a weighted adjoint of $D_+$ when $\langle D_+ v, u\rangle_h = \langle v, T u\rangle_h$ for all $u, v \in \mathbb{R}^N$. If $N \ge 2$ and $h > 0$, then $-D_-$ is a weighted adjoint of $D_+$: $\langle D_+ v, u\rangle_h = \langle v, -D_- u\rangle_h$ for all $u, v$.
