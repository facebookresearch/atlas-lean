# Linearized time-fractional calcium equation under the excess buffer approximation

**Model.** Free cytosolic calcium $C(x,t)$ diffuses along a neuronal process ($x\in\mathbb R$) and reacts with a buffer, $\mathrm{Ca}^{2+}+B\rightleftharpoons \mathrm{CaB}$ with rates $k^+,k^-$, while ER fluxes act as sources and sinks:

$$\partial_t C=D\,\partial_x^2C-k^+[B]\,C+k^-[\mathrm{CaB}]+J_{\rm IPR}-J_{\rm SERCA}+J_{\rm leak}+J_{\rm chan}.$$

Under the excess buffer approximation (buffer far above calcium, so free buffer stays near its background $[B]_\infty$), with the pump and channel terms linearized in a regime $C\ll K_{\rm SERCA}$ or $C\gg K_{\rm SERCA}$, and with memory modelled by a Caputo time derivative of order $u\in(0,1]$, the model is the Caputo time-fractional reaction-diffusion equation

$$ {}^C D_t^{u}C=D\,\partial_x^2C-a\,C+b,\qquad C(x,0)=g(x),$$

where ${}^C D_t^{u}f(t)=\frac{1}{\Gamma(1-u)}\int_0^t(t-\xi)^{-u}f'(\xi)\,d\xi$ for $0<u<1$ and ${}^C D_t^{1}=\partial_t$, $D>0$ is the diffusion coefficient, $a>0$ collects the buffer binding rate $k^+[B]_\infty$ and the linearized flux coefficients, and $b\ge0$ collects the constant source terms (background calcium, ER release). For $u=1$ it is the classical linear reaction-diffusion equation.

## Expansion

A formal Fourier transform in $x$ and Laplace transform in $t$, with $\mathcal L[{}^CD_t^uC]=s^u\tilde C-s^{u-1}C(0)$ and the Laplace pairs $\mathcal L[E_u(-\lambda t^u)]=s^{u-1}/(s^u+\lambda)$ and $\mathcal L[t^{v-1}E_{u,v}(-\lambda t^u)]=s^{u-v}/(s^u+\lambda)$ of the Mittag-Leffler functions $E_u(z)=\sum_{n\ge0}z^n/\Gamma(un+1)$ and $E_{u,v}(z)=\sum_{n\ge0}z^n/\Gamma(un+v)$, gives the candidate solution $C(x,t)=\int_{\mathbb R}G_u(x-y,t)\,g(y)\,dy+b\,t^uE_{u,u+1}(-a\,t^u)$ with $\widehat{G_u}(k,t)=E_u(-(Dk^2+a)\,t^u)$. For $u=1$ this is the heat kernel times $e^{-at}$ plus $(b/a)(1-e^{-at})$; for $u<1$ the source-driven part tends to $b/a$ only algebraically, since $E_u(-z)\sim z^{-1}/\Gamma(1-u)$ as $z\to\infty$, so the order $u$ controls how slowly calcium relaxes after a perturbation. The source's Theorem 1 (Eq. 26) writes this representation with the argument $(Dk^2-a)t^u$, which grows with $k$, and an undefined constant $j_o$; its Theorem 3 is a maximum principle for the equation on $[0,T]\times[0,L]$. Biologically, lowering the buffer concentration lowers $a$, which raises the steady free-calcium level $b/a$; the source uses this to model reduced buffering in Alzheimer's-affected neurons.

## Sources

- Vatsal VH, Jha BK, Singh TP. To study the effect of ER flux with buffer on the neuronal calcium. *The European Physical Journal Plus* 138 (2023). <https://doi.org/10.1140/epjp/s13360-023-04077-z> (PMCID: PMC10240135). Eqs. (3)-(5), (14)-(16) and (27)-(28); Theorems 1 and 3.
