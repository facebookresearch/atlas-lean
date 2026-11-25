# Uniform pair-norm bound for leapfrog iterates

On a periodic grid of $N$ cells with spacing $h$, grid functions are $u, v : \{0, \dots, N-1\} \to \mathbb{R}$, with weighted inner product $\langle u, v\rangle_h = h\sum_j u_j v_j$, $\|u\|_h^2 = \langle u, u\rangle_h$ and pair norm $\|(u, v)\| = \sqrt{\|u\|_h^2 + \|v\|_h^2}$. Let $(D_+ v)_j = (v_{j+1} - v_j)/h$ with indices mod $N$, and $D_+^{\top}$ its transpose matrix. The leapfrog step is $v' = v - c\,\Delta t\, D_+^{\top} u$, $u' = u + c\,\Delta t\, D_+ v'$, and the energy is $Q(u, v) = \|u\|_h^2 + \|v\|_h^2 - \langle u, c\,\Delta t\, D_+ v\rangle_h$.

Let $h > 0$, $c > 0$, $\Delta t > 0$ and $\rho < 1$ with $c\,\Delta t/h \le \rho$. If $(u_n, v_n)$ is the $n$-th leapfrog iterate from $(u_0, v_0)$, then for every $n$,

$$\|(u_n, v_n)\| \le \sqrt{\frac{1 + \rho}{1 - \rho}}\; \|(u_0, v_0)\|.$$
