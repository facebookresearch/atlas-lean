# Singular-perturbation limits of follicle activation and growth models

**Rescaled compartmental model.** Let $x_0$ be the (rescaled) quiescent follicle pool and $x_1,\dots,x_d$ successive growing stages. With a small parameter $\varepsilon>0$ expressing that quiescent follicles are numerous and slowly activated while growth is fast,

$$
\frac{dx_0}{dt}=-\bigl(\lambda_0(x)+\mu_0(x)\bigr)x_0,\qquad \varepsilon\frac{dx_i}{dt}=\lambda_{i-1}(x)x_{i-1}-\bigl(\lambda_i(x)+\mu_i(x)\bigr)x_i,\quad i=1,\dots,d,
$$

with activation/maturation rates $\lambda_i(x)=f_i/(1+K_{1,i}\sum_j\omega_{1,j}x_j)$ and death rates $\mu_i(x)=g_i(1+K_{2,i}\sum_j\omega_{2,j}x_j)$ ($f_d=0$), the feedback terms $K$ expressing inhibition of activation and enhancement of death by growing follicles. Setting $\varepsilon=0$ gives a differential–algebraic limit in which the growing stages are at quasi-steady state driven by $x_0(t)$.

**Proposition (ODE, linear case, Proposition 1).** Assume no feedback ($K_{1,i}=K_{2,i}=0$ for all $i$) and $f_i+g_i>0$ for $i\ge1$. Then for every $\eta>0$, $\sup_{t>\eta}\max_{1\le i\le d}|x_i^\varepsilon(t)-\bar x_i(t)|\to0$ as $\varepsilon\to0$, where

$$
\bar x_0(t)=x_0^{in}e^{-(f_0+g_0)t},\qquad \bar x_i(t)=p_i\,\bar x_0(t),\qquad p_i=\prod_{j=0}^{i-1}\frac{f_j}{f_{j+1}+g_{j+1}} .
$$

**Proposition (stochastic, linear case, Proposition 3).** In the stochastic version, follicles are individuals undergoing activation, stage transitions and death as independent Poisson events with the same rates, the quiescent count is scaled as $X_0^\varepsilon/\varepsilon$, and initially $X_0^{\varepsilon,in}/\varepsilon,X_1^{\varepsilon,in},\dots,X_d^{\varepsilon,in}$ are independent Poisson with means $x_0^{in}/\varepsilon,x_1^{in},\dots,x_d^{in}$. Without feedback and with $f_i+g_i>0$, for every $t>0$, $X_0^\varepsilon(t)\to\bar x_0(t)$ in law and each $X_i^\varepsilon(t)$ converges in law to a Poisson random variable with mean $p_i\bar x_0(t)$. (Proposition 2 is the analogous uniform convergence for the age- or maturity-structured transport PDE model.)

## Expansion

In the linear case the fast subsystem is a lower-triangular linear system $\varepsilon\dot x=Ax+b(t)$ with $A$ having diagonal entries $-(f_i+g_i)<0$, so Tikhonov's theorem applies: after an initial layer of width $O(\varepsilon)$ the fast variables track the unique quasi-steady state $-A^{-1}b(t)$, which is $p_i\bar x_0(t)$ by forward substitution. For the stochastic model the probability generating function solves a linear first-order PDE whose characteristics are explicit; with Poisson initial data it remains a product of Poisson generating functions with means solving the ODE system, which converge to $\bar x_0$ for the slow pool (law of large numbers in $1/\varepsilon$) and to $p_i\bar x_0$ for each stage. With feedback, the limit models are well-posed in specific cases and convergence is shown numerically; they reproduce the bimodal follicle size distribution and the slope break in the decay of the quiescent pool with age.

## Sources

- C. Bonnet, K. Chahour, F. Clément, M. Postel and R. Yvinec, "Multiscale population dynamics in reproductive biology: singular perturbation reduction in deterministic and stochastic models", arXiv:1903.08555 (2019), Section 2 (rescaled ODE model, limit model, Proposition 1), Section 3 (Proposition 2) and Section 4 (Poisson initial condition, Proposition 3), <https://doi.org/10.48550/arXiv.1903.08555>.
