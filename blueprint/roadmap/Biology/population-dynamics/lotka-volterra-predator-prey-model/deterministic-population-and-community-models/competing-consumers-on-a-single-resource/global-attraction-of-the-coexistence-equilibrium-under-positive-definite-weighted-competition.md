# Global attraction of the coexistence equilibrium under positive definite weighted competition

Consider a logistically growing resource $x$ and $n$ consumers $y_1,\dots,y_n$ with linear capture and direct interference competition:

$$
\dot x=x\Big(r\Big(1-\frac xK\Big)-\sum_{j=1}^nq_jy_j\Big),\qquad \dot y_i=y_i\Big(c_iq_ix-\mu_i-\sum_{j=1}^nm_{ij}y_j\Big),\quad i=1,\dots,n,
$$

with positive initial data. Here $r,K>0$ are the intrinsic growth rate and carrying capacity, $q_i>0$ the capture rates, $c_i>0$ the conversion efficiencies, $\mu_i>0$ the mortalities, and $M=(m_{ij})$, with $m_{ij}\ge0$ and $m_{ii}>0$, the matrix of competition coefficients. Define the efficiency-weighted symmetrization of $M$,

$$
L_{\mathbf c}(M)_{ii}=c_i^{-1}m_{ii},\qquad L_{\mathbf c}(M)_{ij}=\tfrac12\big(c_i^{-1}m_{ij}+c_j^{-1}m_{ji}\big)\quad(i\ne j).
$$

**Theorem.** If $E^*=(x^*,y_1^*,\dots,y_n^*)$ is an equilibrium with all coordinates positive and $L_{\mathbf c}(M)$ is positive definite, then $E^*$ attracts the open positive orthant: every solution with initial data in $(0,\infty)^{n+1}$ converges to $E^*$.

**Corollary ($n=2$).** If a positive equilibrium $(x^*,y_1^*,y_2^*)$ exists and

$$
\frac{c_2m_{12}+c_1m_{21}}{2}<\sqrt{c_1m_{11}\,c_2m_{22}},
$$

then every solution with initial data in $(0,\infty)^3$ converges to it.

## Proof sketch

The system is of Lotka–Volterra form $\dot z_k=z_k\big(b_k+(Az)_k\big)$ for $z=(x,y_1,\dots,y_n)$, with

$$
A=\begin{pmatrix}-r/K&-\mathbf q^{\top}\\ D[\mathbf c]\,\mathbf q&-M\end{pmatrix},
$$

where $D[\mathbf c]$ is the diagonal matrix of $\mathbf c$. The criterion of Goh and of Takeuchi and Adachi, in the form of Theorem 1 of Clenet, Massol and Najim (with $A=-I+B$), says: if $A$ is Lyapunov diagonally stable, that is $CA+A^{\top}C$ is negative definite for some positive diagonal matrix $C$, then for every $b$ the system has a unique equilibrium $z^*\ge0$ solving the associated linear complementarity problem, and every solution with positive initial data converges to it. A positive equilibrium solves that problem, so it is $z^*$. (Goh's Lyapunov function is $\sum_kC_{kk}\big(z_k-z_k^*-z_k^*\ln(z_k/z_k^*)\big)$.) Take $C=\mathrm{diag}(1,c_1^{-1},\dots,c_n^{-1})$. The capture terms cancel, so $CA+A^{\top}C$ is block diagonal with blocks $-2r/K$ and $-2L_{\mathbf c}(M)$, which is negative definite exactly when $L_{\mathbf c}(M)$ is positive definite. For $n=2$, positive definiteness of the $2\times2$ matrix $L_{\mathbf c}(M)$ means $c_1^{-1}m_{11}c_2^{-1}m_{22}>\tfrac14\big(c_1^{-1}m_{12}+c_2^{-1}m_{21}\big)^2$; multiplying by $(c_1c_2)^2$ and using $m_{ij}\ge0$ gives the stated inequality.

## Sources

- Maxime Clenet, François Massol and Jamal Najim, "Impact of a block structure on the Lotka-Volterra model", *Peer Community Journal* 4 (2024), e86, <https://doi.org/10.24072/pcjournal.460>. Preprint version: arXiv:2311.09470 (2023), Section 2, the definition of Lyapunov diagonal stability and Theorem 1 (Takeuchi and Adachi: if $-I+B$ is Lyapunov diagonally stable, then for every $\mathbf r$ the system $\dot y_k=y_k(r_k+((-I+B)\mathbf y)_k)$ has a unique equilibrium, the solution of its linear complementarity problem, and every solution with $\mathbf y(0)>0$ converges to it), <https://doi.org/10.48550/arXiv.2311.09470>.
- B. S. Goh, "Global stability in many-species systems", *The American Naturalist* 111 (1977), 135–143, <https://doi.org/10.1086/283144> (the original criterion, with a positive diagonal $C$ making $CA+A^{\top}C$ negative definite).
