# Global attraction of the coexistence equilibrium under positive definite weighted competition

Consider a resource $x$ and $n$ consumers $y_1,\dots,y_n$ with linear capture and direct interference competition:
$$
\dot x=x\Big(r\,g(x)-\sum_{j=1}^nq_jy_j\Big),\qquad \dot y_i=y_i\Big(c_iq_ix-\mu_i-\sum_{j=1}^nm_{ij}y_j\Big),\quad i=1,\dots,n,
$$
with positive initial data. The growth function $g$ is differentiable with $g'(x)<0$ for $x>0$ and $g(K)=0$. Here $r,K>0$ are the intrinsic growth rate and carrying capacity, $q_i>0$ the capture rates, $c_i>0$ the conversion efficiencies, $\mu_i>0$ the mortalities, and $M=(m_{ij})$ the matrix of competition coefficients. Define the efficiency-weighted symmetrization of $M$,
$$
L_{\mathbf c}(M)_{ii}=c_i^{-1}m_{ii},\qquad L_{\mathbf c}(M)_{ij}=\tfrac12\big(c_i^{-1}m_{ij}+c_j^{-1}m_{ji}\big)\quad(i\ne j).
$$

**Theorem.** If $E^*=(x^*,y_1^*,\dots,y_n^*)$ is a positive equilibrium and $L_{\mathbf c}(M)$ is positive definite, then $E^*$ attracts every solution with positive initial data.

**Corollary ($n=2$).** If
$$
\frac{c_2m_{12}+c_1m_{21}}{2}<\sqrt{c_1m_{11}\,c_2m_{22}},
$$
then the positive equilibrium $(x^*,y_1^*,y_2^*)$ is a global attractor. Interspecific interference weaker than the geometric mean of the weighted self-limitation therefore guarantees stable coexistence of two consumers on one resource, even though in the absence of interference only one consumer would persist on a single resource. The system is also dissipative: all non-negative solutions eventually enter a fixed compact set. For one consumer it is uniformly persistent when its break-even resource level $x_1^b=\mu_1/(c_1q_1)$ is below $K$.

## Expansion

Use the Volterra-type Lyapunov function
$$
V=\int_{x^*}^x\frac{s-x^*}{s}\,ds+\sum_{i=1}^n\frac{1}{c_i}\Big(y_i-y_i^*-y_i^*\ln\frac{y_i}{y_i^*}\Big).
$$
The capture terms cancel. Since $g$ is decreasing, the resource part of $\dot V$ is non-positive, and the consumer part is $-(\mathbf y-\mathbf y^*)^\top L_{\mathbf c}(M)(\mathbf y-\mathbf y^*)$. Positive definiteness makes $\dot V\le0$ with equality only at $E^*$, and LaSalle's invariance principle gives global attraction. For $n=2$, positive definiteness of the $2\times2$ matrix is exactly the stated inequality after multiplying by $c_1c_2$.

## Sources

- A. Reyes-García, "Competencia y Depredación: el Arribo de una Especie Exótica al Medio", arXiv:2302.14841 (2023), Chapter 2 (system (2.1), Teorema 2.1, Definición 2.2, Teorema 2.7, Teorema 2.19, Corolario 2.20). <https://doi.org/10.48550/arXiv.2302.14841>
