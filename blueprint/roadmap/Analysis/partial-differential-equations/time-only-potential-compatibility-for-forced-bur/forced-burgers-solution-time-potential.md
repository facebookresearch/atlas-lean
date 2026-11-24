# Purely time-dependent potentials give unforced Burgers

Let $\nu>0$, $T\ge0$, and let $u_0:\mathbb R\to\mathbb R$ be continuous and bounded by one real constant in absolute value. Suppose $r:\mathbb R\to\mathbb R$ is continuous on $[0,T]$.

For every spatial anchor $a$, time $t\in[0,T]$ and point $x\in\mathbb R$, the actual forced Burgers construction with potential $q(s,y)=r(s)$ equals the unforced heat-kernel Burgers construction with the same viscosity, datum and anchor:

$$U_\nu(r,u_0,a)(t,x)=U_\nu(0,u_0,a)(t,x).$$

The right side is the ordinary unforced Burgers initial-value evolution. The potential has no spatial forcing because its spatial derivative vanishes. No derivative of $r$ or $u_0$, and no bounded initial primitive, is required. Both strip endpoints and the zero horizon are included. Only continuity of $r$ on the strip is needed, so temporal corners and arbitrary exterior values are permitted.
