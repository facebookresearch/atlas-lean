# Reproduction number of a dengue model with active case finding

**Model.** Mosquitoes are susceptible, exposed or infectious ($S_v,E_v,I_v$; recruitment $\pi_v$, death $\mu_v$, incubation rate $\gamma_v$). Humans (recruitment $\pi_h$, death $\mu_h$) enter a high-risk susceptible class $S_{h1}$ with probability $r$ and a low-risk class $S_{h2}$ otherwise; low-risk individuals are infected at relative rate $\theta<1$. After incubation (rate $\gamma_h$) a fraction $\rho$ becomes asymptomatic ($A_h$, relative infectiousness $\lambda$) and $1-\rho$ symptomatic ($I_h$). Symptomatic cases are hospitalized or notified ($P_h$) at rate $\eta$, and *active case finding* moves asymptomatic and symptomatic cases into $P_h$ at rates $p_1$ and $p_2$; $A_h,I_h,P_h$ recover at rates $q_1,q_2,q_3$ and $P_h$ suffers disease death $\delta$. With biting rate $\beta$ and transmission probabilities $\alpha_v$ (mosquito to human) and $\alpha_h$ (human to mosquito),

$$\dot E_v=\beta\alpha_hS_v\frac{I_h+\lambda A_h}{N_h}-(\gamma_v+\mu_v)E_v,\qquad \dot E_h=\beta\alpha_vI_v\frac{S_{h1}+\theta S_{h2}}{N_h}-(\gamma_h+\mu_h)E_h ,$$

$$\dot A_h=\rho\gamma_hE_h-(\mu_h+q_1+p_1)A_h,\qquad \dot I_h=(1-\rho)\gamma_hE_h-(\mu_h+\eta+q_2+p_2)I_h,$$

together with the susceptible, $I_v$, $P_h$ and $R_h$ equations. Notified cases do not transmit.

**Theorem.** The solutions enter and remain in a bounded positively invariant region, and the basic reproduction number (spectral radius of the next-generation matrix) is

$$\mathcal R_0^2=\frac{\beta^2\pi_v\alpha_v\alpha_h\mu_h\gamma_v\gamma_h\{r+\theta(1-r)\}}{\mu_v^2\pi_h(\gamma_v+\mu_v)(\gamma_h+\mu_h)}\Bigl[\frac{\lambda\rho}{\mu_h+q_1+p_1}+\frac{1-\rho}{\mu_h+\eta+q_2+p_2}\Bigr].$$

The disease-free equilibrium is locally asymptotically stable if $\mathcal R_0<1$ and unstable if $\mathcal R_0>1$; an endemic equilibrium $E^*$, when it exists, is globally asymptotically stable in the invariant region under explicit sufficient inequalities on the parameters (which also exclude persistent oscillations). $\mathcal R_0$ is strictly decreasing in the case-finding rates $p_1,p_2$ and in the notification rate $\eta$, and depends on $\beta$ and $\mu_v$ through squared factors, so vector control remains the strongest lever while case finding of asymptomatic infections reduces the human-to-vector term.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

The infected compartments are $(E_v,I_v,E_h,A_h,I_h,P_h)$; at the disease-free state $S_v=\pi_v/\mu_v$, $N_h=\pi_h/\mu_h$ and $(S_{h1}+\theta S_{h2})/N_h=r+\theta(1-r)$. The next-generation matrix has a two-step host–vector cycle, so $\mathcal R_0$ is the geometric mean of the vector-to-host number $\beta\alpha_v\{r+\theta(1-r)\}\frac{\pi_v\mu_h}{\mu_v\pi_h}\frac{\gamma_v}{(\gamma_v+\mu_v)\mu_v}$ and the host-to-vector number $\beta\alpha_h\frac{\gamma_h}{\gamma_h+\mu_h}\bigl[\frac{\lambda\rho}{\mu_h+q_1+p_1}+\frac{1-\rho}{\mu_h+\eta+q_2+p_2}\bigr]$, each the product of a transmission rate, the probability of surviving incubation and the mean infectious period. Local stability follows from the van den Driessche–Watmough theorem.

## Sources

- Indrajit Ghosh, Pankaj Kumar Tiwari, Joydev Chattopadhyay, "Effect of active case finding on dengue control: Implications from a mathematical model", Journal of Theoretical Biology 464 (2019), 50–62, <https://doi.org/10.1016/j.jtbi.2018.12.027>. Published version of arXiv:1808.08123, cited next; locators there refer to the arXiv version.
- I. Ghosh, P. K. Tiwari, J. Chattopadhyay, "Effect of active case finding on dengue control: Implications from a mathematical model", arXiv:1808.08123 (2018), Section 2 (model and Lemma 2.1), Section 3 (next-generation computation of $\mathcal R_0$ and Theorem 3.1) and Section 4 (Theorem 4.1). <https://doi.org/10.48550/arXiv.1808.08123>
