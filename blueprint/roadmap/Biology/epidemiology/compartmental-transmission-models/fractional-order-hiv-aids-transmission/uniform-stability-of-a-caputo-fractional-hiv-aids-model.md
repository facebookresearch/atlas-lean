# Uniform stability of a Caputo fractional HIV/AIDS model with chronic stage

**Model.** For $\alpha\in(0,1)$ let ${}^C_{t_0}D^\alpha_t$ be the Caputo derivative. Susceptibles $S$, HIV-infected without AIDS symptoms $I$, infected under ART with a viral load low enough to be chronic $C$, and AIDS patients $A$ satisfy

$${}^CD^\alpha S=\Lambda-\beta(I+\eta_CC+\eta_AA)S-\mu S,\qquad {}^CD^\alpha I=\beta(I+\eta_CC+\eta_AA)S-(\rho+\phi+\mu)I+\omega C+\gamma A,$$

$${}^CD^\alpha C=\phi I-(\omega+\mu)C,\qquad {}^CD^\alpha A=\rho I-(\gamma+\mu+d)A,$$

with recruitment $\Lambda$, natural death $\mu$, AIDS death $d$, relative infectiousness $\eta_C,\eta_A$, progression rates $\rho,\phi$ and return rates $\omega,\gamma$ (treatment). The region $\Omega=\{(S,I,C,A)\in\mathbb R^4_+:S+I+C+A\le\Lambda/\mu\}$ is feasible. With $\xi_1=\gamma+\mu+d$, $\xi_2=\omega+\mu$,

$$\mathcal N=\beta\bigl(\xi_2(\xi_1+\rho\eta_A)+\eta_C\phi\xi_1\bigr),\qquad \mathcal D=\mu\bigl(\xi_2(\rho+\xi_1)+\phi\xi_1+\rho d\bigr)+\rho\omega d,\qquad R_0=\frac{\Lambda}{\mu}\frac{\mathcal N}{\mathcal D}.$$

**Equilibria.** The disease-free equilibrium is $\Sigma_0=(\Lambda/\mu,0,0,0)$. If $R_0>1$ there is a unique endemic equilibrium

$$S^*=\frac{\mathcal D}{\mathcal N},\quad I^*=\frac{\xi_1\xi_2(\Lambda\mathcal N-\mu\mathcal D)}{\mathcal D\mathcal N},\quad C^*=\frac{\phi\xi_1(\Lambda\mathcal N-\mu\mathcal D)}{\mathcal D\mathcal N},\quad A^*=\frac{\rho\xi_2(\Lambda\mathcal N-\mu\mathcal D)}{\mathcal D\mathcal N}.$$

**Theorem.** For every order $\alpha\in(0,1)$:

1. if $R_0<1$, $\Sigma_0$ is uniformly asymptotically stable in $\Omega$;
2. if $R_0>1$, $\Sigma_*$ is uniformly asymptotically stable in the interior of $\Omega$.

The threshold is therefore the same as for the integer-order model and independent of the memory order $\alpha$.

## Expansion

Uniform asymptotic stability of Caputo systems follows from a fractional Lyapunov theorem: a $C^1$ function $L$ squeezed between positive definite $W_1\le L\le W_2$ with ${}^CD^\alpha L\le-W_3$ certifies it. The needed differential inequality comes from the estimate

$${}^CD^\alpha\Bigl[x-x^*-x^*\ln\frac{x}{x^*}\Bigr]\le\Bigl(1-\frac{x^*}{x}\Bigr){}^CD^\alpha x ,$$

which lets Volterra-type Lyapunov functions from the classical model carry over. For $\Sigma_0$ a linear combination $c_1I+c_2C+c_3A$ has fractional derivative bounded by a negative multiple of the infected states when $R_0<1$; for $\Sigma_*$ a weighted sum of the logarithmic terms in all four variables yields a nonpositive bound by the arithmetic–geometric mean inequality, vanishing only at $\Sigma_*$. Local stability can alternatively be read from Matignon's criterion that all eigenvalues of the Jacobian satisfy $|\arg\lambda|>\alpha\pi/2$.

## Sources

- Cristiana J. Silva, Delfim F.M. Torres, "Stability of a fractional HIV/AIDS model", Mathematics and Computers in Simulation 164 (2019), 180–190, <https://doi.org/10.1016/j.matcom.2019.03.016>. Published version of arXiv:1903.02534, cited next; locators there refer to the arXiv version.
- C. J. Silva, D. F. M. Torres, "Stability of a fractional HIV/AIDS model", arXiv:1903.02534 (2019), Section 2 (Definition 2.1, Theorem 2.3, Lemma 2.4) and Section 3 (model, $R_0$, equilibria, Theorems 3.1–3.2). <https://doi.org/10.48550/arXiv.1903.02534>
