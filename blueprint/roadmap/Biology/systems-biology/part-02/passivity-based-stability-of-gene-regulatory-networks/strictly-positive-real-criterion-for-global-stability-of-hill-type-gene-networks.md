# Strictly positive real criterion for global stability of Hill-type gene networks

**Model.** Let $m\in\mathbb{R}^n$ be mRNA and $p\in\mathbb{R}^m$ protein concentrations in a regulatory network with additive (SUM-logic) regulation:

$$\dot m_i = -k_{m_i}m_i + \sum_j b_{ij}(p_j),\qquad \dot p_j = -k_{p_j}p_j + k_{d_{ji}}m_i,$$

where each regulation term is a Hill function, $b_{ij}(p_j) = \alpha_{ij}g(p_j)$ for an activator and $\alpha_{ij} - \alpha_{ij}g(p_j)$ for a repressor, with

$$g(p) = \frac{(p/\beta)^H}{1 + (p/\beta)^H},\qquad \beta > 0,\ H\ \text{the Hill coefficient}.$$

With $x = (m,p)$ this is a Lur'e system

$$\dot x = A_cx - B_c\,g(C_cx) + l,\qquad A_c = \begin{pmatrix}A & 0\\ D & C\end{pmatrix},\quad B_c = \begin{pmatrix}B\\ 0\end{pmatrix},\quad C_c = (0\ \ I_m),$$

where $A = \operatorname{diag}(-k_{m_i})$, $C = \operatorname{diag}(-k_{p_j})$, $D$ holds the translation constants, $B_{ij}\in\{0, -\alpha_{ij}, \alpha_{ij}\}$ encodes no regulation, activation ($+\alpha_{ij}g$ requires $B_{ij} = -\alpha_{ij}$) or repression ($\alpha_{ij} - \alpha_{ij}g$ requires $B_{ij} = \alpha_{ij}$), and $l$ collects the constant parts $\alpha_{ij}$ of repressor terms.

**Sector condition.** $g$ is increasing, so for all $p$ and increments $e$, componentwise and in vector form,

$$0\le e^{\mathsf T}\big(g(p + e) - g(p)\big)\le\gamma\,e^{\mathsf T}e,$$

with $\gamma$ a bound on $g'$ over the relevant range.

**Lemma (passivity criterion).** Let $x^\ast$ be an equilibrium. If $(A_c, B_c, C_c)$ is controllable and observable and the transfer matrix $G(s) = C_c(sI - A_c)^{-1}B_c$ is strictly positive real, i.e. there exist symmetric positive definite $P$ and positive definite $Q$ with

$$PA_c + A_c^{\mathsf T}P = -Q,\qquad PB_c = C_c^{\mathsf T},$$

then $x^\ast$ is globally exponentially stable.

## Expansion

With $e = x - x^\ast$ the error obeys $\dot e = A_ce - B_c\big[g(C_ce + C_cx^\ast) - g(C_cx^\ast)\big]$. For $V(e) = \tfrac12 e^{\mathsf T}Pe$ the two matrix identities give

$$\dot V = -\tfrac12 e^{\mathsf T}Qe - (C_ce)^{\mathsf T}\big[g(C_ce + C_cx^\ast) - g(C_cx^\ast)\big]\le -\tfrac12 e^{\mathsf T}Qe,$$

the last term being non-negative by the sector condition. This is the Kalman–Yakubovich–Popov route to absolute stability: the linear degradation–translation part is passive and the monotone Hill feedback is in the sector $[0,\infty)$, so stability holds for every Hill nonlinearity in the sector, not just one. A small-gain alternative uses only the upper sector bound: $\sup_\omega\lVert G(j\omega)\rVert < 1/\gamma$. The same Lyapunov function, augmented with parameter-error terms, underlies adaptive control laws that steer the network to a desired steady state by adjusting transcription rates and keep errors bounded under bounded additive noise.

## Sources

- Y. Jin, M. Lindsey, *Stability analysis of genetic regulatory network with additive noises*, BMC Genomics 9 (Suppl. 1) (2008), S21, model (Eqs. 1–6) and Methods (Lemma 1, Eqs. 8–10, Remarks 1–2). <https://doi.org/10.1186/1471-2164-9-s1-s21> (PMCID: PMC2386064)
