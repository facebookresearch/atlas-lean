# Mean-square stability of the stochastic intracellular calcium model

**Setting.** The slow–fast intracellular calcium concentration (ICC) model of FitzHugh–Nagumo type couples a fast membrane variable $x$, a slow recovery variable $y$ and the intracellular calcium level $z$:

$$\dot x=\tau\big(b_0y+b_1x-x^3-\phi_f(z)\big),\qquad \dot y=\tau\varepsilon k\,(a_0x+a_1y+a_2),\qquad \dot z=\tau\varepsilon\Big(\phi_r(x)-\frac{z-z_b}{\tau_z}\Big),$$

with $0<\varepsilon\ll1$, $\tau,k,z_b,\tau_z>0$, $b_1>0>b_0$, $a_0>0$, $-1\ll a_1<0$, $a_2>0$, calcium feedback $\phi_f(z)=\mu z/(z+z_0)$ and sigmoidal calcium release $\phi_r(x)=\lambda/(1+e^{-\rho(x-x_{on})})$, $\mu,z_0,\lambda,\rho>0$. The stochastic model perturbs the electrical and recovery equations only:

$$dX_t=f_1(\xi_t)\,dt+g_1(\xi_t)\,dW^1_t,\qquad dY_t=f_2(\xi_t)\,dt+\sqrt\varepsilon\,g_2(\xi_t)\,dW^2_t,\qquad dZ_t=f_3(\xi_t)\,dt,$$

where $\xi_t=(X_t,Y_t,Z_t)$, $f_1,f_2,f_3$ are the right-hand sides above and $W^1,W^2$ are independent Brownian motions; the $\sqrt\varepsilon$ scaling matches the slow drift of $Y$. Let $\mathcal R=\mathbb R^2\times\mathbb R_+$.

**Theorem.**
1. (Positivity) If $Z_0>0$ then $Z_t>0$ for all $t\in[0,T]$.
2. (Well-posedness) If $g_1,g_2$ are locally Lipschitz and $\tfrac12g_1(\xi)^2+\tfrac12\varepsilon g_2(\xi)^2\le K(1+\|\xi\|^2)$ on $\mathcal R$, then for every $\xi_0\in\mathcal R$ there is a unique strong solution in $\mathcal R$.
3. (Mean-square stability) Suppose in addition that the deterministic model has a unique globally asymptotically stable equilibrium $(x^*,y^*,z^*)$ and that the growth constant satisfies

$$K<\min\Big\{\frac{\tau b_0a_1}{2a_0\beta},\ \frac{\tau\varepsilon}{2\tau_z\beta}\Big\},\qquad \beta=\max\Big\{1,-\frac{b_0}{\varepsilon k a_0}\Big\}.$$

Then for every $\xi_0\in\mathcal R$ there is $C>0$ with

$$\limsup_{t\to\infty}\frac1t\,\mathbb E\int_0^t\Big((X_s-x^*)^2+(Y_s-y^*)^2+(Z_s-z^*)^2\Big)\,ds\le C,$$

so the solution stays, on time average, in a mean-square neighbourhood of the deterministic equilibrium whose size is controlled by the noise intensity.

The same three statements hold for the six-dimensional model of two diffusively coupled cells, with the analogous noise bound $K<\frac{\tau\varepsilon}{2}\min\{-k_1a_1,-k_2a_1,1/\tau_z\}$.

## Expansion

Positivity of $Z$ follows from the variation-of-constants formula for the linear $z$-equation with positive forcing $\phi_r(X_t)$ and positive baseline $z_b$. For stability, apply Itô's formula to the weighted quadratic Lyapunov function $V=\tfrac12(X-x^*)^2+\tfrac\alpha2(Y-y^*)^2+\tfrac12(Z-z^*)^2$ with $\alpha=-b_0/(\varepsilon k a_0)$ chosen to cancel the cross terms between $x$ and $y$. The cubic term and the negative $a_1$, $-1/\tau_z$ terms give a negative-definite drift, the Lipschitz feedbacks $\phi_f,\phi_r$ are absorbed with Young's inequality, and the bound on $K$ keeps the Itô correction $\tfrac12g_1^2+\tfrac12\alpha\varepsilon g_2^2$ from destroying negativity. Integrating $\mathbb E\,LV\le -c\,\mathbb E\|\xi-\xi^*\|^2+D$ and dividing by $t$ gives the time-averaged bound.

## Sources

- Tomás Caraballo, Macarena Gómez-Mármol, Ignacio Roldán, "A Stochastic Model of Intracellular Calcium Concentrations", arXiv:2609.13213 (2026), model (ICC) of Section 1, Theorems 2.2, 2.3 and 2.4, and Theorems 4.1–4.3, <https://doi.org/10.48550/arXiv.2609.13213>.
