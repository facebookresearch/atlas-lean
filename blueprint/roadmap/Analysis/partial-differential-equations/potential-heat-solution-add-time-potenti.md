# Time-only gauge for the actual potential-heat solution

Let $\nu>0$ and $T\ge0$. For every $s\in[0,T]$, suppose $q(s,\cdot)$ is $C^2$. For each $k=0,1,2$, assume the actual spatial derivative $\partial_x^kq$ is jointly continuous on $[0,T]\times\mathbb R$ and uniformly bounded there:

$$\forall k\le2\quad\exists C_k\in\mathbb R\quad\forall(s,y)\in[0,T]\times\mathbb R,\qquad |\partial_x^kq(s,y)|\le C_k.$$

Let $r:\mathbb R\to\mathbb R$ be continuous on $[0,T]$. No time derivative of $q$ or $r$ is assumed, and $r$ is unrestricted outside the strip.

Let $g:\mathbb R\to\mathbb R$ be continuous with exponential growth: there exist $M,c\ge0$ such that $|g(y)|\le M e^{c|y|}$ for all $y$. Let $H_\nu(q,g)$ denote the actual potential-heat Volterra evolution with viscosity $\nu$, potential $q$ and initial datum $g$. Then for every $t\in[0,T]$ and $x\in\mathbb R$,

$$H_\nu(q+r,g)(t,x)=\exp\left(\int_0^t r(s)\,ds\right)H_\nu(q,g)(t,x),$$

where $(q+r)(s,y)=q(s,y)+r(s)$.

The datum may be signed, unbounded, and nonintegrable on the whole line. The identity includes both endpoints and $T=0$. The positive sign is essential: differentiating the factor adds $r(t)$ to the potential. The product's actual PDE, initial values and uniform exponential growth identify it with the Volterra construction by classical uniqueness; no mild representation is supplied as a premise.

This integrating-factor identity is the normalization mechanism in Gesztesy and Holden, [The Cole–Hopf and Miura transformations revisited](https://arxiv.org/abs/solv-int/9812025), Theorem 3.3 and Remark 3.4.
