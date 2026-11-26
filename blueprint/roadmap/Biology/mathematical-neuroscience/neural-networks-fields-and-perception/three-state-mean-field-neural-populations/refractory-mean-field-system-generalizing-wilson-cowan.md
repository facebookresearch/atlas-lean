# Refractory mean-field system generalizing Wilson–Cowan

Neurons are sensitive, active or refractory. In population $J$ a sensitive neuron activates at rate $\alpha_JF_J(B_J)$, an active one becomes refractory at rate $\beta_J$, and a refractory one becomes sensitive at rate $\gamma_J$, where $F_J\ge 0$ is an increasing response function and $B_J=\sum_K c_{JK}A_K+Q_J$ is the input, with $c_{JK}=|K|W_{JK}$. With the mean-field closure (covariances neglected), the active, refractory and sensitive fractions $A_J,R_J,S_J=1-A_J-R_J$ satisfy

$$\dot A_J=-\beta_JA_J+\alpha_JF_J(B_J)S_J,\qquad \dot R_J=-\gamma_JR_J+\beta_JA_J,\qquad \dot S_J=-\alpha_JF_J(B_J)S_J+\gamma_JR_J,$$

a $2n$-dimensional system on $\mathcal D_n=\{(A_J,R_J)_J: A_J,R_J\ge 0,\ A_J+R_J\le 1\}$.

**Proposition 1.** $\mathcal D_n$ is invariant under the flow.

**Wilson–Cowan reduction.** Fixing each refractory fraction at its equilibrium value $R_J=\frac{\beta_J}{\gamma_J}A_J$ gives the $n$-dimensional subsystem

$$\dot A_J=-\beta_JA_J+\alpha_JF_J(B_J)\Bigl(1-\bigl(1+\tfrac{\beta_J}{\gamma_J}\bigr)A_J\Bigr),$$

which is Wilson and Cowan's equation with $\tau_J=1/\beta_J$, refractory period $r_J=1/\beta_J+1/\gamma_J$, $f_J=\alpha_JF_J$ and $w_{JK}=c_{JK}/\beta_K$ written for the firing rate $\beta_JA_J$. Both systems have the same fixed points.

**Proposition 2.** The Wilson–Cowan domain $\mathcal D_n^{\mathrm{WC}}=\{R_J=\tfrac{\beta_J}{\gamma_J}A_J\ \forall J\}$ is not invariant under the full flow; hence it is not an attracting set and the Wilson–Cowan subsystem is not stable inside the full system.

**Proposition 3.** For one population with self-coupling $c$, if $\beta+\gamma>\alpha c\sup F'$ the system has no periodic orbits in $\mathcal D_1$; in particular a single inhibitory population ($c<0$) never oscillates, while a single excitatory population can.

## Expansion

On a boundary face where some fraction vanishes, its derivative is a sum of nonnegative terms, so the field points into $\mathcal D_n$. For Proposition 2, at a point of $\mathcal D_n^{\mathrm{WC}}$ with $A_K=x$ chosen so that $\frac{\alpha_K\gamma_K}{\alpha_K\beta_K+\alpha_K\gamma_K+\beta_K\gamma_K}<x<\frac{\gamma_K}{\beta_K+\gamma_K}$ and $F_K$ suitably placed, the field has a nonzero component normal to the subspace, so it is not tangent. For Proposition 3 the divergence of the planar field is $-\beta-\gamma-\alpha F+\alpha c(1-A-R)F'\le-\beta-\gamma+\alpha c\sup F'<0$, and Bendixson's criterion excludes cycles. The extra refractory dimension is what lets an excitatory population oscillate, and two excitatory populations already produce chaotic dynamics in numerical examples.

## Sources

- V. Painchaud, N. Doyon, P. Desrosiers, "Beyond Wilson–Cowan dynamics: oscillations and chaos without inhibition", Biological Cybernetics 116(5–6) (2022) 527–543, <https://doi.org/10.1007/s00422-022-00941-w>, PMCID PMC9691500. Eqs. (4)–(11), Propositions 1–3 and the Corollary to Proposition 2.
