# Admissible mean–variance setpoints for protein-number control

**Model.** In the two-stage gene expression network $\varnothing \xrightarrow{k_r} \text{mRNA}$, $\text{mRNA} \xrightarrow{\gamma_r} \varnothing$, $\text{mRNA} \xrightarrow{k_p} \text{mRNA} + \text{protein}$, $\text{protein} \xrightarrow{\gamma_p} \varnothing$ (all rates positive), the propensities are affine, so the first two moments of the chemical master equation close exactly. With $x_1, x_2$ the mean mRNA and protein numbers and $x_3, x_4, x_5$ the entries of the covariance matrix, $\dot x_1 = k_r - \gamma_r x_1$, $\dot x_2 = k_p x_1 - \gamma_p x_2$, and the covariance equations are linear in $(x_1,\dots,x_5)$ with input $k_r$. The system is asymptotically stable (Property 1) with equilibrium (Property 2)

$$x_1^* = \frac{k_r}{\gamma_r},\quad x_2^* = \frac{k_pk_r}{\gamma_p\gamma_r},\quad x_3^* = \frac{k_r}{\gamma_r},\quad x_4^* = \frac{k_pk_r}{\gamma_r(\gamma_p + \gamma_r)},\quad x_5^* = \frac{k_pk_r(\gamma_p + k_p + \gamma_r)}{\gamma_p\gamma_r(\gamma_p + \gamma_r)} .$$

To control both the stationary mean $\mu_*$ and variance $\sigma_*^2$ of the protein number, use two inputs: the transcription rate $u_1 = k_r$ and the mRNA degradation rate $u_2 = \gamma_r$ (the moment system becomes bilinear).

**Proposition 10.** The set of reference pairs $(\mu_*, \sigma_*^2)$ that are stationary values of the closed loop for some nonnegative constant inputs is the open nonempty set

$$\mathcal{A} = \Big\{(x, y) \in \mathbb{R}_{>0}^2 :\ x < y < \Big(1 + \frac{k_p}{\gamma_p}\Big)x\Big\},$$

and for $(\mu_*, \sigma_*^2) \in \mathcal{A}$ the equilibrium inputs are unique:

$$u_2^* = -\gamma_p + \frac{k_p\mu_*}{\sigma_*^2 - \mu_*}, \qquad u_1^* = \frac{\gamma_p}{k_p}\mu_* u_2^* .$$

The lower bound $\sigma_*^2 > \mu_*$ (protein noise is always super-Poissonian) does not depend on the controller structure or on parameter knowledge, so no controller acting through these rates can push the Fano factor to $1$ or below. If instead $\gamma_p$ is the second input, the upper factor becomes $1 + k_p/\gamma_r$; if $k_p$ is, the upper bound disappears.

## Depends on

- [Positive PI control of the mean protein number](positive-pi-control-of-mean-protein-number.md)

## Expansion

From the closed-moment equilibrium, the protein Fano factor is $x_5^*/x_2^* = 1 + k_p/(\gamma_r + \gamma_p)$, which exceeds $1$ for every positive $\gamma_r$; this gives the lower bound. Solving $\sigma_*^2/\mu_* = 1 + k_p/(u_2 + \gamma_p)$ for $u_2$ gives $u_2^*$, which is positive exactly when $\sigma_*^2 < (1 + k_p/\gamma_p)\mu_*$; then the mean equation $\mu_* = k_p u_1/(\gamma_p u_2)$ gives $u_1^* > 0$. The setpoint region is thus a cone between Fano factors $1$ and $1 + k_p/\gamma_p$, and the paper then studies local stabilization of setpoints in this region by integral feedback acting on both inputs.

## Sources

- Corentin Briat and Mustafa Khammash, "Computer control of gene expression: Robust setpoint tracking of protein mean and variance using integral feedback", 2012 IEEE 51st IEEE Conference on Decision and Control (CDC) (2012), 3582–3588, <https://doi.org/10.1109/cdc.2012.6426720>; numbering as in arXiv:1207.4766: Properties 1–3, Lemmas 4 and 5, Theorem 6 and Proposition 10.
