# Control reproduction number and quarantine-benefit threshold of the SEQAIJR model

**Model.** Susceptible $S$, exposed $E$, quarantined $Q$, asymptomatic $A$, symptomatic $I$, isolated $J$ and recovered $R$ individuals, $N=S+E+Q+A+I+J+R$:

$$\begin{aligned}S'&=\Pi-\tfrac{\beta S(I+r_QQ+r_AA+r_JJ)}{N}-\mu S, & E'&=\tfrac{\beta S(I+r_QQ+r_AA+r_JJ)}{N}-(\gamma_1+k_1+\mu)E,\\ Q'&=\gamma_1E-(k_2+\sigma_1+\mu)Q, & A'&=pk_1E-(\sigma_2+\mu)A,\\ I'&=(1-p)k_1E-(\gamma_2+\sigma_3+\mu)I, & J'&=k_2Q+\gamma_2I-(\delta+\sigma_4+\mu)J,\end{aligned}$$

and $R'=\sigma_1Q+\sigma_2A+\sigma_3I+\sigma_4J-\mu R$. Here $\gamma_1$ is the quarantine rate of exposed people, $\gamma_2$ the isolation rate of symptomatic people, $r_Q,r_A,r_J$ relative infectiousness, $\delta$ disease-induced death. Write $a=\gamma_1+k_1+\mu$, $q=k_2+\sigma_1+\mu$, $s=\sigma_2+\mu$, $i=\gamma_2+\sigma_3+\mu$, $j=\delta+\sigma_4+\mu$.

**Control reproduction number.** By the next-generation method,

$$R_c=\frac{\beta}{a}\Big[\frac{r_Q\gamma_1}{q}+\frac{r_Apk_1}{s}+\frac{(1-p)k_1}{i}+\frac{r_J\gamma_1k_2}{qj}+\frac{r_J(1-p)k_1\gamma_2}{ij}\Big].$$

**Theorem.**

*(1)* The disease-free equilibrium is locally and globally asymptotically stable if $R_c<1$ and unstable if $R_c>1$.

*(2)* A unique endemic equilibrium exists iff $R_c>1$, and it is locally asymptotically stable (forward transcritical bifurcation at $R_c=1$).

*(3)* *(Quarantine threshold.)* $\partial R_c/\partial\gamma_1<0$, i.e. quarantining exposed individuals has a positive population-level impact, iff $r_Q<r_{\gamma_1}$, where

$$r_{\gamma_1}=\frac{q}{k_1+\mu}\Big[\frac{r_Apk_1}{s}+\frac{(1-p)k_1}{i}\Big]+\frac{r_J\,q}{(k_1+\mu)j}\Big[\frac{(1-p)k_1\gamma_2}{i}-\frac{k_2(k_1+\mu)}{q}\Big];$$

if $r_Q>r_{\gamma_1}$, more quarantine raises $R_c$. The threshold $r_{\gamma_1}$ can be negative (the source's display asserts $r_{\gamma_1}>0$, which fails for some parameters), in which case quarantine raises $R_c$ for every $r_Q\ge 0$.

*(4)* *(Isolation threshold.)* Analogously, isolation of symptomatic individuals lowers $R_c$ iff $r_J$ is below an explicit threshold $r_{\gamma_2}$.

## Expansion

$R_c$ sums the expected secondary infections produced along the four routes out of $E$: quarantine then isolation, asymptomatic, symptomatic, and symptomatic then isolation, each weighted by relative infectiousness and time spent in the class. Quarantine moves people from the routes through $A$ and $I$ into the route through $Q$; this helps only if quarantined people are sufficiently less infectious than the average of the routes they leave, which is exactly $r_Q<r_{\gamma_1}$. The model was fitted to daily UK case data for short-term forecasts.

## Sources

- Sk Shahid Nadim, Indrajit Ghosh and Joydev Chattopadhyay, "Short-term predictions and prevention strategies for COVID-19: A model based study", arXiv:2003.08150 (2020), system (2.1), the next-generation computation of $R_c$, and Theorems 3.1–3.6 of Section 3, <https://doi.org/10.48550/arXiv.2003.08150>.
