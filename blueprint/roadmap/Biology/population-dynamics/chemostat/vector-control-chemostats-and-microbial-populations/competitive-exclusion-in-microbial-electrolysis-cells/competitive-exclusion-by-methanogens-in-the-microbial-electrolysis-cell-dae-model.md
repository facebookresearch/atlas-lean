# Competitive exclusion by methanogens in the microbial electrolysis cell DAE model

**Model.** A microbial electrolysis cell is a chemostat-like reactor with dilution rate $D$ and influent substrate $S_0$, containing $n_m$ methanogen species $X_{m,j}$ and $n_e$ electroactive bacteria $X_{e,j}$, an oxidized extracellular mediator $M$ (total pool $M_{\rm total}$) and current $I$. The semi-explicit index-1 differential-algebraic system is

$$
\begin{aligned}
\dot S&=D(S_0-S)-\sum_j\frac{\mu_{m,j}(S)}{y_{m,j}}X_{m,j}-\sum_j\frac{\mu_{e,j}(S,M)}{y_{e,j}}X_{e,j},\\
\dot X_{m,j}&=\big(\mu_{m,j}(S)-K_{d,m,j}\big)X_{m,j},\qquad \dot X_{e,j}=\big(\mu_{e,j}(S,M)-K_{d,e,j}\big)X_{e,j},\\
\dot M&=\gamma I-Y_M\sum_j\frac{\mu_{e,j}(S,M)}{y_{e,j}}X_{e,j},\\
0&=\Delta E-R_{\rm int}(\mathbf X_e)I-\frac{RT}{mF}\Big[\ln\frac{M_{\rm total}}{M_{\rm total}-M}+2\,\mathrm{arcsinh}\frac{I}{2A_{\rm sur}I_0}\Big],
\end{aligned}
$$

with Monod kinetics $\mu_{m,j}(S)=\mu_{\max,m,j}\frac{S}{K_{S,m,j}+S}$ and dual-limited $\mu_{e,j}(S,M)=\mu_{\max,e,j}\frac{S}{K_{S,e,j}+S}\frac{M}{K_{M,j}+M}$. Only electroactive bacteria produce current, hence hydrogen.

**Break-even concentrations.** Zero net growth occurs at

$$
\lambda_{m,j}=\frac{K_{S,m,j}K_{d,m,j}}{\mu_{\max,m,j}-K_{d,m,j}},\qquad
\lambda_{e,j}(M)=\frac{K_{S,e,j}K_{d,e,j}}{\mu_{\max,e,j}\frac{M}{K_{M,j}+M}-K_{d,e,j}},
$$

a level for methanogens but a curve in the $(M,S)$-plane for electroactive bacteria. Let $M_0=M_{\rm total}\big(1-e^{-mF\Delta E/(RT)}\big)$ be the mediator level solving the constraint at $I=0$, and $\Lambda=\{\lambda_{m,j}\}_j\cup\{\lambda_{e,j}(M_0)\}_j$.

**Theorem.** Assume initial data lie in the positively invariant compact region $\Omega_G$ ($0<S\le S_0$, $0<M\le M_0$, bounded positive concentrations and current) and every break-even value is attainable ($\lambda_{m,j}\in(0,S_0]$, and $\lambda_{e,j}(M)\in(0,S_0]$ for some $M\in(0,M_0]$; otherwise that species goes extinct).

1. *(Competitive exclusion by methanogens.)* If $\lambda_{m,1}<\min(\Lambda\setminus\{\lambda_{m,1}\})$, all solutions converge to the methanogen-only equilibrium

$$
P_m=\Big(S=\lambda_{m,1},\ X_{m,1}=\frac{D(S_0-\lambda_{m,1})\,y_{m,1}}{\mu_{m,1}(\lambda_{m,1})},\ \text{all other }X=0,\ M=M_0,\ I=0\Big).
$$

2. *(Coexistence of tied methanogens.)* If $\lambda=\lambda_{m,1}=\dots=\lambda_{m,k}$ is strictly smaller than the other elements of $\Lambda$, solutions approach the set where $S=\lambda$, only $X_{m,1},\dots,X_{m,k}$ are positive with $D(S_0-\lambda)=\sum_{j\le k}\mu_{m,j}(\lambda)X_{m,j}/y_{m,j}$, $M=M_0$ and $I=0$.

## Expansion

The proof extends Hsu's chemostat Lyapunov function:

$$
V=\int_{\lambda_{m,1}}^{S}\frac{\sigma-\lambda_{m,1}}{\sigma}d\sigma+c_{m,1}\int_{X^*_{m,1}}^{X_{m,1}}\frac{\xi-X^*_{m,1}}{\xi}d\xi+\sum_{j\ge2}c_{m,j}X_{m,j}+\sum_jc_{e,j}X_{e,j},
$$

with $c_{m,j}=\mu_{\max,m,j}/\big(y_{m,j}(\mu_{\max,m,j}-K_{d,m,j})\big)$ and $c_{e,j}$ the analogous constant evaluated at $M_0$. Writing the growth laws as $(\mu_{\max}-K_d)\frac{S-\lambda}{K_S+S}$ and using $M\le M_0$ (so $\lambda_{e,j}(M)\ge\lambda_{e,j}(M_0)>\lambda_{m,1}$) makes every competitor term carry the factor $\lambda_{m,1}-\lambda_{\cdot,j}<0$, so $\dot V\le0$ on $\Omega_G$; LaSalle's principle applied on the constraint manifold of the index-1 DAE gives convergence. The practical message is negative for hydrogen production: if a methanogen breaks even at the lowest substrate level for all attainable mediator levels, electroactive bacteria wash out and current vanishes. When an electroactive species has the lowest break-even curve for some $M$, the outcome is decided by the algebraic current constraint and is not settled by this argument.

## Proof depends on

- [LaSalle's invariance principle](../../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Sources

- Harry J. Dudley, Zhiyong Jason Ren, David M. Bortz, "Competitive Exclusion in a DAE Model for Microbial Electrolysis Cells", arXiv:1906.02086 (2019), Section 2 (LaSalle for semi-explicit DAEs, Theorem 1), Section 4: Lemmas 1–2, Theorem 2 (competitive exclusion by methanogens) and Corollary 1 (coexistence), <https://doi.org/10.48550/arXiv.1906.02086>.
