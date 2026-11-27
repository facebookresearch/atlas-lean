# Lyapunov-exponent criterion for robust permanence of interacting structured populations

**Model.** $k$ interacting populations, population $i$ structured into $n_i$ states with state vector $x_i\in\mathbb R^{n_i}_{\ge0}$, evolve by

$$\frac{dx_i}{dt}=A_i(x)\,x_i,\qquad i=1,\dots,k,\qquad x=(x_1,\dots,x_k)\in C=\prod_i\mathbb R^{n_i}_{\ge0},$$

where (A1) $x\mapsto A_i(x)$ is continuous; (A2) each $A_i(x)$ is an irreducible matrix with non-negative off-diagonal entries (no negative feedback between states of the same population); (A3) solutions exist for all $t\ge0$; (A4) the semiflow is dissipative. It is **permanent** if, in addition, there is a global attractor contained in the positive cone $C^+$ whose basin is $C^+$; it is **robustly permanent** if every system $\dot x_i=\tilde A_i(x)x_i$ with $\tilde A$ uniformly close to $A$ (and satisfying A1–A4) is permanent.

**Invasion rates.** Let $B_i(t,x)$ be the fundamental matrix of the linear system $\dot y=A_i(x.t)\,y$ along the orbit $x.t$. The invasion rate of population $i$ at $x$ is $\lambda_i(x)=\limsup_{t\to\infty}\frac1t\ln\|B_i(t,x)\|$; it equals $\limsup\frac1t\ln|B_i(t,x)v|$ for every positive $v$, and $\limsup\frac1t\int_0^t\langle A_i(x.s)u_i(x.s),u_i(x.s)\rangle\,ds$ for the normalized direction $u_i$. For an ergodic invariant measure $\mu$, $\lambda_i(x)$ is $\mu$-a.e. constant, $\lambda_i(\mu)$; if $\mu$ gives positive mass to $\{x_i\ne0\}$ (population $i$ present), then $\lambda_i(\mu)=0$.

**Theorem.**

1. (Robustly unsaturated sets) Let $K$ be a compact isolated invariant subset of the boundary $\partial C$. If $\max_i\lambda_i(\mu)>0$ for every invariant measure $\mu$ supported in $K$, equivalently if there are weights $p_i>0$ with $\sum_ip_i\lambda_i(\mu)>0$ for every ergodic $\mu$ supported in $K$, then $K$ is robustly unsaturated (some missing population invades, also after small perturbations). Conversely, if $A$ is $C^2$ and $K$ is robustly unsaturated, then $\max_i\lambda_i(\mu)>0$ for all ergodic $\mu$ on $K$.
2. (Robust permanence) If $\{M_1,\dots,M_m\}$ is a Morse decomposition of the boundary dynamics and $\max_i\lambda_i(\mu)>0$ for all invariant measures supported on each $M_j$, then the system is robustly permanent. Conversely, if $A$ is $C^2$ and some ergodic measure supported on a Morse component violates the condition, the system is not robustly permanent.
3. If $A$ is $C^2$ and each Morse component is Axiom A, uniquely ergodic, or has all but one population strictly positive, then robust permanence holds if and only if $\max_i\lambda_i(\mu)>0$ for all ergodic $\mu$ supported in the Morse components.
4. The system and all of its subsystems are robustly permanent if and only if $\lambda_i(\mu)>0$ for every ergodic $\mu$ supported in $\partial C$ and every population $i$ absent from the support of $\mu$.

## Expansion

The sufficiency direction builds an average Lyapunov function $P(x)=\prod_i\langle v_i,x_i\rangle^{p_i}$ along the boundary: by the multiplicative ergodic theorem, $\frac1t\ln\langle v_i,x_i(t)\rangle$ grows at rate $\lambda_i$ near an ergodic measure, and positivity of $\sum_ip_i\lambda_i(\mu)$ for all ergodic $\mu$ on $K$ (a minimax/convexity argument over invariant measures turns $\max_i\lambda_i>0$ into a single weight vector) makes $P$ increase on average near $K$, so $K$ repels the interior uniformly. Since the condition is an open condition in $A$ (invasion rates depend continuously on $A$ over the compact set of invariant measures), it persists under perturbation. Applying this to each Morse component and using the acyclicity of the Morse decomposition gives a repelling boundary, hence permanence by standard results (Garay, Hofbauer–So). For the converse, a $C^2$ perturbation can make an ergodic measure with $\max_i\lambda_i(\mu)\le0$ attract nearby interior orbits.

## Sources

- Josef Hofbauer, Sebastian J. Schreiber, "Robust permanence for interacting structured populations", arXiv (2010); Journal of Differential Equations 248 (2010). Section 2 (model and assumptions A1–A4), Section 3 (Proposition 1, Theorem 1), Section 4 (Theorem 2 after Garay and Hofbauer–So, Theorem 3, Corollaries 3 and 4). <https://doi.org/10.48550/arXiv.1005.4146>. Published version: Journal of Differential Equations 248(8) (2010), 1955–1971, <https://doi.org/10.1016/j.jde.2009.11.010>; locators above refer to the arXiv version.
