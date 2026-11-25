# The actual potential-heat evolution for the sine potential

Let $\nu>0$. Let $H_\nu(q,g)$ denote the actual Volterra potential-heat evolution with potential $q$ and initial datum $g$. For every $t\ge0$ and $x\in\mathbb R$,

$$H_\nu(q_\nu,1)(t,x)=\exp(t\sin x),\qquad q_\nu(t,x)=\sin x+\nu t\sin x-\nu t^2\cos^2x.$$

The right-hand side has initial value one, satisfies the actual equation $\Phi_t=\nu\Phi_{xx}+q_\nu\Phi$, and is uniformly bounded by $e^T$ on each strip $[0,T]\times\mathbb R$. Classical uniqueness identifies it with the constructed evolution. Smoothness and all uniform derivative bounds of the potential are proved separately; no solution identity or growth bound is supplied as a premise.

This example is obtained by direct substitution in the forced Cole–Hopf identity of Gesztesy and Holden, [The Cole–Hopf and Miura transformations revisited](https://arxiv.org/abs/solv-int/9812025), Theorem 3.3.
