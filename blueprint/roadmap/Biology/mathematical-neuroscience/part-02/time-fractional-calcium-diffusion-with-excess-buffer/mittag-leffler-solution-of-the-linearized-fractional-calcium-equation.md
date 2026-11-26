# Mittag-Leffler solution of the linearized time-fractional calcium equation

**Setting.** Free cytosolic calcium $C(x,t)$ diffuses along a neuronal process ($x\in\mathbb R$) and reacts with a buffer $B+\mathrm{Ca}^{2+}\rightleftharpoons \mathrm{CaB}$ (rates $k^+,k^-$), with ER fluxes ($J_{\rm IPR}$, $J_{\rm SERCA}$, $J_{\rm leak}$, $J_{\rm chan}$) as sources and sinks. Under the excess buffer approximation (buffer far above calcium, so free buffer stays near its background $[B]_\infty$) and with the pump and channel terms linearized in a regime $C\ll K_{\rm SERCA}$ or $C\gg K_{\rm SERCA}$, the dynamics with memory are modelled by the Caputo time-fractional reaction-diffusion equation of order $u\in(0,1]$,

$$ {}^C D_t^{u}C=D\,\partial_x^2C-a\,C+b,\qquad C(x,0)=g(x),$$

where $D>0$, $a>0$ collects the buffer binding rate $k^+[B]_\infty$ and the linearized flux coefficients, and $b\ge0$ collects the constant source terms (background calcium, ER release).

**Statement.** For bounded integrable $g$, the bounded solution is

$$C(x,t)=\int_{\mathbb R}G_u(x-y,t)\,g(y)\,dy\;+\;b\,t^{u}E_{u,u+1}\!\big(-a\,t^{u}\big),\qquad \widehat{G_u}(k,t)=E_u\!\big(-(Dk^2+a)\,t^{u}\big),$$

that is, $G_u(x,t)=\frac1\pi\int_0^\infty E_u(-(Dk^2+a)t^u)\cos(kx)\,dk$, where $E_u(z)=\sum_{n\ge0}z^n/\Gamma(un+1)$ and $E_{u,v}(z)=\sum_{n\ge0}z^n/\Gamma(un+v)$ are the Mittag-Leffler functions. For $u=1$ this is the heat kernel times $e^{-at}$ plus $(b/a)(1-e^{-at})$. For every $u\in(0,1]$ the source-driven part tends to the steady level $b/a$ as $t\to\infty$, but only algebraically for $u<1$, since $E_u(-z)\sim z^{-1}/\Gamma(1-u)$ as $z\to\infty$; the order $u$ therefore controls how slowly calcium relaxes after a perturbation.

## Expansion

Take the Fourier transform in $x$ and the Laplace transform in $t$. Using $\mathcal L{}^CD_t^uC=s^u\tilde C-s^{u-1}C(0)$ gives $\tilde C(k,s)=\frac{s^{u-1}\hat g(k)}{s^u+Dk^2+a}+\frac{\hat b(k)}{s\,(s^u+Dk^2+a)}$, where $\hat b$ is the transform of the constant source. The Laplace pairs $\mathcal L[E_u(-\lambda t^u)]=s^{u-1}/(s^u+\lambda)$ and $\mathcal L[t^{v-1}E_{u,v}(-\lambda t^u)]=s^{u-v}/(s^u+\lambda)$ (here $v=u+1$) invert both terms; a spatially constant source only excites $k=0$, which gives the $x$-independent term. The source derives the Green's-function representation by Fourier cosine and Laplace transforms (its Theorem 1), expresses it through Mainardi and Wright functions (Theorem 2), and proves uniqueness via a maximum principle for the fractional operator (Theorem 3); the statement above is written with the decaying argument $-(Dk^2+a)t^u$ required for a bounded solution. Biologically, lowering the buffer concentration lowers $a$, which raises the steady free-calcium level $b/a$; the source uses this to model reduced buffering in Alzheimer's-affected neurons.

## Sources

- Vatsal VH, Jha BK, Singh TP. To study the effect of ER flux with buffer on the neuronal calcium. *The European Physical Journal Plus* 138 (2023). <https://doi.org/10.1140/epjp/s13360-023-04077-z> (PMCID: PMC10240135). Eqs. (15)-(17), (27); Theorems 1-3.
