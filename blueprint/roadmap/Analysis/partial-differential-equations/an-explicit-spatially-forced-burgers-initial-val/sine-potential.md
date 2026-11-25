# The sine potential for an explicit forced solution

For real viscosity parameter $\nu$ and real time and space coordinates, define

$$q_\nu(t,x)=\sin x+\nu t\sin x-\nu t^2\cos^2x.$$

This is the potential associated with the strictly positive profile $\Phi(t,x)=\exp(t\sin x)$: direct differentiation gives $\Phi_t=\nu\Phi_{xx}+q_\nu\Phi$. For $\nu>0$, its Cole–Hopf velocity is $-2\nu t\cos x$ and starts from zero. The potential varies in space, so its spatial derivative supplies a nonzero Burgers forcing.

This example is obtained by direct substitution in the forced Cole–Hopf identity of Gesztesy and Holden, [The Cole–Hopf and Miura transformations revisited](https://arxiv.org/abs/solv-int/9812025), Theorem 3.3.
