# The forward-difference matrix represents the forward difference

On the $N$-element periodic grid $\{0, \dots, N - 1\}$ (empty when $N = 0$) with spacing $h \in \mathbb{R}$, let $(D_+ v)_j = (v_{j+1} - v_j)/h$, indices taken modulo $N$, with the convention $a/0 = 0$, so that $D_+ = 0$ when $h = 0$. For every $v$, the matrix of $D_+$ times $v$ equals $D_+ v$.
