# Global structural identifiability of the linear ERK model

**Linear ERK model.** Let $S_0,S_1,S_2$ be the concentrations of unphosphorylated, singly and doubly phosphorylated ERK under MEK action, with

$$\dot S_0=-\kappa_1S_0,\qquad \dot S_1=-\kappa_2S_1+(1-\pi)\kappa_1S_0,\qquad \dot S_2=\pi\kappa_1S_0+\kappa_2S_1,$$

parameters $\kappa_1,\kappa_2>0$ and processivity $\pi\in[0,1)$, and initial condition $S_0(0)=5$, $S_1(0)=S_2(0)=0$. It is the quasi-steady-state reduction of the mass-action model in which $\kappa_i=E_{tot}k_{f_i}k_{c_i}/(k_{c_i}+k_{r_i})$ and $\pi=k_{c_2}/(k_{c_2}+k_{r_2})$. The solution is $S_0=5e^{-\kappa_1t}$, $S_2=5-S_0-S_1$ and

$$S_1(t)=\begin{cases}\dfrac{5\kappa_1(1-\pi)}{\kappa_1-\kappa_2}\bigl(e^{-\kappa_2t}-e^{-\kappa_1t}\bigr),&\kappa_1\ne\kappa_2,\\[1ex] 5\kappa_1(1-\pi)\,t\,e^{-\kappa_1t},&\kappa_1=\kappa_2.\end{cases}$$

**Definitions.** For time points $t_1,\dots,t_l$, the model prediction map $\phi_{t_1,\dots,t_l}$ sends a parameter to the vector of outputs at those times, and $\theta\sim\theta'$ when $\phi(\theta)=\phi(\theta')$. The model is **globally identifiable** if every equivalence class has one element, **generically identifiable** if this holds off a proper subvariety, and **locally identifiable** if almost all classes are finite. It is **practically identifiable** at a data point $z^*$ and level $\alpha$ if the likelihood-ratio confidence region $U_\delta(z^*)$ is bounded in parameter space; with i.i.d. Gaussian noise, $U_\delta(z^*)=\phi^{-1}(B_\rho(z^*))$ is the preimage of a Euclidean ball around the data.

**Theorem.** For any three distinct nonzero time points, $\phi_{t_1,t_2,t_3}$ of the linear ERK model is injective on $\{(\kappa_1,\kappa_2,\pi)\}$, so the model is globally structurally identifiable; with the experimental design of the paper (seven time points, replicates, five MEK variants) it is also practically identifiable.

## Expansion

$S_0(t_1)$ determines $\kappa_1$. If two triples share $\kappa_1$, the difference of their $S_1$ trajectories is, after multiplying by $e^{\kappa_1t}$, a function of the form $Ae^{\alpha t}-Be^{\beta t}+C$ (or with a linear term $(1-\pi)t$ when $\kappa_1=\kappa_2$). It vanishes at $t=0$, and unless it vanishes identically such a function has at most two real zeros, hence at most one positive zero; the paper computes it explicitly as $t=\log\bigl((1-\pi)/(1-\pi')\bigr)/(\kappa_1-\kappa_2')$. Agreement at three distinct positive times therefore forces the trajectories to coincide, and then $\kappa_2=\kappa_2'$ and $\pi=\pi'$. Sontag's theorem guarantees that $2m+1$ generic time points suffice for an $m$-parameter rational model, but deciding identifiability at specified time points without closed-form solutions is open. The paper also shows that, unlike the linear model, the full and rational mass-action ERK models have unbounded numerical confidence regions; nearby quasi-steady-state parameter values, where the reduction is exact and the fibre of $\phi$ is positive-dimensional, are a plausible source.

## Sources

- L. Marsh, E. Dufresne, H. M. Byrne, H. A. Harrington, "Algebra, geometry and topology of ERK kinetics", Bulletin of Mathematical Biology 84(12) (2022) 137, <https://doi.org/10.1007/s11538-022-01088-2>, PMCID PMC9588486. Eqs. (9)–(11), Definitions 5 and 8, Theorem 1, Section 4 and Appendix A.4, Eqs. (16)–(17).
