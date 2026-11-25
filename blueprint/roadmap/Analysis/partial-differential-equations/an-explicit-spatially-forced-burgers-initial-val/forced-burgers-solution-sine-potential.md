# The actual forced Burgers evolution for the sine potential

Let $\nu>0$ and choose any spatial anchor $a\in\mathbb R$. Let $U_\nu(q,u_0,a)$ be the actual forced Burgers initial-value construction, obtained by taking the logarithmic derivative of the potential-heat evolution of the initial Cole–Hopf profile. For zero initial velocity and the potential

$$q_\nu(t,x)=\sin x+\nu t\sin x-\nu t^2\cos^2x,$$

the constructed solution satisfies, for every $t\ge0$ and $x\in\mathbb R$,

$$U_\nu(q_\nu,0,a)(t,x)=-2\nu t\cos x.$$

The formula includes the initial time and is independent of the anchor. It follows by first identifying the actual potential-heat profile as $\exp(t\sin x)$ and then differentiating its spatial slice. For positive time the resulting field satisfies $u_t+u u_x-\nu u_{xx}=-2\nu\partial_xq_\nu$. Its initial value is $u(0,x)=0$. Both the nonzero spatial forcing and the nonlinear transport term occur in this example.

This example is obtained by direct substitution in the forced Cole–Hopf identity of Gesztesy and Holden, [The Cole–Hopf and Miura transformations revisited](https://arxiv.org/abs/solv-int/9812025), Theorem 3.3.
