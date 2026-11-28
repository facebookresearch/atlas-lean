# Adjoint of the forward difference

On the $N$-element periodic grid $\{0, \dots, N - 1\}$ (empty when $N = 0$) with spacing $h \in \mathbb{R}$, let $(D_+ v)_j = (v_{j+1} - v_j)/h$, indices taken modulo $N$, with the convention $a/0 = 0$, so that $D_+ = 0$ when $h = 0$. The transposed operator $D_+^{\mathsf T}$ is the transpose of the matrix of $D_+$, applied to $u$; it is defined for every $h$. For $h > 0$ the form $h \sum_j u_j v_j$ is an inner product and $D_+^{\mathsf T}$ is the adjoint of $D_+$ for it.
