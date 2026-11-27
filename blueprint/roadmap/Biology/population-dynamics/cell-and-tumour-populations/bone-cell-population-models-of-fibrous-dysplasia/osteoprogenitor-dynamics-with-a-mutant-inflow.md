# Osteoprogenitor dynamics with a mutant inflow

**Model.** Let $P$, $P_m$, $P_p$ be wild-type, mutant and phenocopying (wild-type cells induced by mutants to behave like them) osteoprogenitors, $C_I$ osteocytes and $C_L$ osteoclasts, with total occupancy $M=P+P_m+P_p+C_I$:

$$\dot P=\rho P(1-M)+\tau_s(1-\mu M)-\alpha P-\delta_mPP_m,\qquad \dot P_m=\rho_mP_m(1-M)+\tau_m(1-\mu M),$$

$$\dot P_p=\rho_mP_p(1-M)+\delta_mPP_m,\qquad \dot C_I=\alpha P-\delta C_IC_L,\qquad \dot C_L=\tau_cM-\gamma_cC_L .$$

Here $\rho,\rho_m$ are proliferation rates in a shared niche of capacity $1$, $\tau_s,\tau_m$ are inflows from stem cells damped by the occupancy factor $1-\mu M$, $\alpha$ is differentiation into osteocytes, $\delta_m$ the phenocopying rate, and osteoclasts recruited in proportion to $M$ resorb osteocytes. Setting $P_m=P_p=0$ gives the healthy bone model $\dot P=\rho P(1-M)+\tau_s(1-\mu M)-\alpha P$, $\dot C_I=\alpha P-\delta C_IC_L$, $\dot C_L=\tau_cM-\gamma_cC_L$, $M=P+C_I$.

**Well-posedness.** For positive parameters and initial data, both models have a unique maximal nonnegative solution, which is bounded; under $1-\mu M>0$ along the solution it is global and positive.

**Healthy bone equilibrium.** If $\rho<\alpha$, the healthy bone model has a unique nonnegative equilibrium, and it is uniformly asymptotically stable.

## Depends on

- [Logistic growth equation](../../logistic-growth-equation/README.md)

## Expansion

Boundedness follows because the right side of each progenitor equation is a downward parabola in its own variable, with linear and constant coefficients bounded once the occupancy satisfies $\mu M<1$; the osteoclast equation is linear and the osteocyte equation is dissipative. In the healthy model, $\rho<\alpha$ means differentiation outpaces self-renewal, so progenitors are maintained by the regulated inflow and the osteocyte–osteoclast loop settles at a unique balance. With a mutant inflow $\tau_m>0$ and $\rho_m$ not small, mutants have no differentiation outflow and also recruit wild-type cells by phenocopying, so the numerical study shows mutant and phenocopying progenitors becoming the main populations even for a small mutant departure fraction.

## Sources

- M. Soloviova, J. C. Beltran Vargas, L. Fernandez de Castro, J. Belmonte-Beitia, "A mathematical model for fibrous dysplasia: The role of the flow of mutant cells", *Bulletin of Mathematical Biology* 86(9) (2024), 108, Section 2 (FD model and healthy bone model), Propositions 1–5, Section 4.3, <https://doi.org/10.1007/s11538-024-01336-7> (preprint arXiv:2402.07724).
