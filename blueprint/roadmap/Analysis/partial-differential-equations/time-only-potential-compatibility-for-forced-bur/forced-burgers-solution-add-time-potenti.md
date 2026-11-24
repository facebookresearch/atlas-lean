# Invariance of forced Burgers under a time-only potential correction

Let $\nu>0$ and $T\ge0$. For every $s\in[0,T]$, suppose $q(s,\cdot)$ is $C^2$. For each $k=0,1,2$, assume the actual spatial derivative $\partial_x^kq$ is jointly continuous on $[0,T]\times\mathbb R$ and uniformly bounded there:

$$\forall k\le2\quad\exists C_k\in\mathbb R\quad\forall(s,y)\in[0,T]\times\mathbb R,\qquad |\partial_x^kq(s,y)|\le C_k.$$

Let $r:\mathbb R\to\mathbb R$ be continuous on $[0,T]$. No time derivative of $q$ or $r$ is assumed, and $r$ is unrestricted outside the strip.

Let $u_0:\mathbb R\to\mathbb R$ be bounded and continuous, with one $M\in\mathbb R$ satisfying $|u_0(y)|\le M$ for every $y$. For any anchor $a$, let $U_\nu(q,u_0,a)$ be the logarithmic derivative $-2\nu\Phi_x/\Phi$ of the actual potential-heat evolution of

$$g_a(y)=\exp\left(-\frac1{2\nu}\int_a^y u_0(z)\,dz\right).$$

Then for every $t\in[0,T]$ and $x\in\mathbb R$,

$$U_\nu(q+r,u_0,a)(t,x)=U_\nu(q,u_0,a)(t,x).$$

No derivative or bounded primitive of $u_0$ is required. The equality includes both endpoints. The profiles differ by the strictly positive scalar $\exp(\int_0^t r)$, independent of space. Their entire spatial slices therefore have proportional derivatives, and this scalar cancels from the logarithmic derivative.

This integrating-factor identity is the normalization mechanism in Gesztesy and Holden, [The Cole–Hopf and Miura transformations revisited](https://arxiv.org/abs/solv-int/9812025), Theorem 3.3 and Remark 3.4.
