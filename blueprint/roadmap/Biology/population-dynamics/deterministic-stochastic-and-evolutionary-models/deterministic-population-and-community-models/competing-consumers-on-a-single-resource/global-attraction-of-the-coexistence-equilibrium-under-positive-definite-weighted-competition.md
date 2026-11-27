# Global attraction of the coexistence equilibrium under positive definite weighted competition

Consider a logistically growing resource $x$ and $n$ consumers $y_1,\dots,y_n$ with linear capture and direct interference competition:

$$
\dot x=x\Big(r\Big(1-\frac xK\Big)-\sum_{j=1}^nq_jy_j\Big),\qquad \dot y_i=y_i\Big(c_iq_ix-\mu_i-\sum_{j=1}^nm_{ij}y_j\Big),\quad i=1,\dots,n,
$$

with positive initial data. Here $r,K>0$ are the intrinsic growth rate and carrying capacity, $q_i>0$ the capture rates, $c_i>0$ the conversion efficiencies, $\mu_i>0$ the mortalities, and $M=(m_{ij})$, with $m_{ij}\ge0$ and $m_{ii}>0$, the matrix of competition coefficients. Define the efficiency-weighted symmetrization of $M$,

$$
L_{\mathbf c}(M)_{ii}=c_i^{-1}m_{ii},\qquad L_{\mathbf c}(M)_{ij}=\tfrac12\big(c_i^{-1}m_{ij}+c_j^{-1}m_{ji}\big)\quad(i\ne j).
$$

**Theorem.** If $E^*=(x^*,y_1^*,\dots,y_n^*)$ is an equilibrium with all coordinates positive and $L_{\mathbf c}(M)$ is positive definite, then $E^*$ is globally asymptotically stable in the open positive orthant $(0,\infty)^{n+1}$.

**Corollary ($n=2$).** If a positive equilibrium $(x^*,y_1^*,y_2^*)$ exists and

$$
\frac{c_2m_{12}+c_1m_{21}}{2}<\sqrt{c_1m_{11}\,c_2m_{22}},
$$

then it is globally asymptotically stable in $(0,\infty)^3$.

## Proof sketch

The system is of Lotka–Volterra form $\dot z_k=z_k\big(b_k+(Az)_k\big)$ for $z=(x,y_1,\dots,y_n)$, with

$$
A=\begin{pmatrix}-r/K&-\mathbf q^{\top}\\ D[\mathbf c]\,\mathbf q&-M\end{pmatrix},
$$

where $D[\mathbf c]$ is the diagonal matrix of $\mathbf c$. Goh's criterion says that a positive equilibrium of such a system is globally asymptotically stable in the open positive orthant whenever $CA+A^{\top}C$ is negative definite for some positive diagonal matrix $C$; the Lyapunov function is $\sum_kC_{kk}\big(z_k-z_k^*-z_k^*\ln(z_k/z_k^*)\big)$. Take $C=\mathrm{diag}(1,c_1^{-1},\dots,c_n^{-1})$. The capture terms cancel, so $CA+A^{\top}C$ is block diagonal with blocks $-2r/K$ and $-2L_{\mathbf c}(M)$, which is negative definite exactly when $L_{\mathbf c}(M)$ is positive definite. For $n=2$, positive definiteness of the $2\times2$ matrix $L_{\mathbf c}(M)$ means $c_1^{-1}m_{11}c_2^{-1}m_{22}>\tfrac14\big(c_1^{-1}m_{12}+c_2^{-1}m_{21}\big)^2$; multiplying by $(c_1c_2)^2$ and using $m_{ij}\ge0$ gives the stated inequality.

## Sources

- B. S. Goh, "Global stability in many-species systems", *The American Naturalist* 111 (1977), 135–143, <https://doi.org/10.1086/283144> (global stability of Lotka–Volterra systems with a positive diagonal $C$ making $CA+A^{\top}C$ negative definite).
