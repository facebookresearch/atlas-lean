# Structural identifiability of a two-patch respiratory infection model

**Model.** Target cells $T_j$, infected cells $I_j$ and virus $V_j$ in the upper ($j=u$) and lower ($j=l$) respiratory tract evolve by

$$\begin{aligned}
\dot T_u&=-\beta_uT_uV_u, & \dot I_u&=\beta_uT_uV_u-\delta_uI_u, & \dot V_u&=p_uI_u-c_uV_u+k_lV_l,\\
\dot T_l&=-\beta_lT_lV_l, & \dot I_l&=\beta_lT_lV_l-\delta_lI_l, & \dot V_l&=p_lI_l-c_l\frac{V_l}{V_l+K}V_l+k_uV_u,
\end{aligned}$$

with infection rates $\beta_j$, infected-cell death rates $\delta_j$, virion production rates $p_j$, linear clearance $c_u$ in the upper tract, saturating clearance with maximum $c_l$ and half-saturation $K$ in the lower tract, and virus transfer rates $k_u$ (upper to lower) and $k_l$ (lower to upper). Only the viral loads $y_1=V_u(t)$ and $y_2=V_l(t)$ are observed.

**Definition.** The model is structurally (globally) identifiable from $(y_1,y_2)$ if $y_i(t,p)=y_i(t,q)$ for all $t$ and $i=1,2$ implies $p=q$; with the differential-algebra approach this is checked by requiring that equality of the coefficients of the monic input–output equations implies equality of parameters.

**Result.**

1. The model is not structurally identifiable: $\beta_u,\delta_u,c_u,k_u,\beta_l,\delta_l,c_l,K,k_l$ are globally identifiable, but $p_u$ and $p_l$ are not.
2. After rescaling the unobserved states, $\hat T_j=p_jT_j$, $\hat I_j=p_jI_j$, the model becomes the same system with $p_u=p_l=1$, and this scaled model is globally structurally identifiable from $(V_u,V_l)$.

## Expansion

Eliminating the unobserved states gives two differential polynomials in $y_1,y_2$ and their derivatives (one of order three in $y_1$, one of order three in $y_2$, the latter made monic by dividing by $k_u$). Their coefficients are rational functions of the parameters, and solving $c(p)=c(q)$ returns equality of all parameters except $p_u,p_l$, which do not appear. The reason is a scaling symmetry: for any $\sigma>0$, $(\sigma T_u,\sigma I_u,V_u,\sigma T_l,\sigma I_l,V_l)$ solves the same equations with $p_j$ replaced by $p_j/\sigma$, leaving the observed viral loads unchanged. Fixing the scale removes the symmetry. In practice the scaled model can still be practically non-identifiable from sparse, noisy data, especially without early-infection measurements.

## Sources

- S. M. Ciupe, N. Tuncer, "Identifiability of parameters in mathematical models of SARS-CoV-2 infections in humans", Scientific Reports (2022), Methods, Eq. (1); Identifiability analysis, Definitions 1–2, Eqs. (3)–(7), Propositions 1–2, <https://doi.org/10.1038/s41598-022-18683-x>, PMCID PMC9418662.
