# Quarantine efficacy as a phase-type escape probability

**Stage model.** For a pathogen variant $X$, an infected individual passes through a non-infectious latent stage $L_1$ (rate $\epsilon_1$), an infectious latent stage $L_2$ (rate $\epsilon_2$), after which a fraction $p \in [0,1]$ becomes detected ($D_1 \to D_2$) and $1-p$ stays undetected ($U_1 \to U_2$), each infectious stage being left at rate $\gamma$ (so the infectious period is Erlang with mean $2/\gamma$); detected cases end in recovery $R^D$ or death $M$ (case fatality $\delta$), undetected cases in removal $R^U$. With transmission rate $\beta$, relative infectiousness $\eta$ of $L_2$ and $\xi$ of detected cases, and initial susceptible population $S(0)$, the single-variant reproduction number is

$$\mathcal R_0 = \beta\Big(\frac{\eta}{\epsilon_2} + \frac{2p\xi}{\gamma} + \frac{2(1-p)}{\gamma}\Big) S(0).$$

**Quarantine efficacy.** Order the nine states as $(L_1, L_2, D_1, D_2, U_1, U_2, R^D, R^U, M)$ and let $T = [t_{ij}]$ be the generator, $t_{ij}$ the rate from state $j$ to state $i$ (columns of absorbing states are zero, diagonal entries make columns sum to zero). The state distribution $C(t)$ of one individual satisfies $C'(t) = T C(t)$, so $C(t) = e^{Tt}C(0)$. Let $u = (1,1,0,0,1,1,0,0,0)$ be the indicator of the *unobserved infected* states $\{L_1, L_2, U_1, U_2\}$. Travellers arrive at Poisson rate $\lambda$ with initial state distribution $C(0)$ supported on these states (detected cases do not travel) and are held without contacts for $t_q$ time units. The **quarantine efficacy** is

$$c(t_q) = 1 - u\, e^{T t_q} C(0),$$

the probability that at release the traveller is detected, dead, or removed rather than still in an unobserved infected state.

**Proposition.**
1. $c(t_q) \in [0,1]$ is non-decreasing in $t_q$, with $c(0) = 0$ when $C(0)$ is supported on unobserved states and $c(t_q) \to 1$ as $t_q \to \infty$.
2. If arrivals form a Poisson process of rate $\lambda$ and travellers evolve independently, the releases that still carry an unobserved infection form a Poisson process of rate $\lambda_q = (1 - c(t_q))\lambda$, entering the community with distribution proportional to the unobserved-state entries of $e^{Tt_q}C(0)$.

## Expansion

$u\,e^{Tt}C(0)$ is the probability that a continuous-time Markov chain on the stage graph has not yet been absorbed into the detected or removed states, i.e. the survival function of a phase-type distribution. Since the unobserved states form a transient block from which mass can only flow out (to detected or removed states), this survival function decreases to $0$, which gives part 1. Part 2 is Poisson thinning: each arrival independently survives quarantine undetected with probability $1-c$, and independent marking of a Poisson process yields a Poisson process. With two stages per phase and the default $C(0) = (\tfrac14, \tfrac14, 0,0, \tfrac14, \tfrac14, 0,0,0)$, a 7-day quarantine reached an efficacy of about $98.4\%$ for the parameters used, i.e. the effective importation rate fell roughly sixtyfold. The same thinning explains why full border closure helps only when started early: once a few undetected importations seed community transmission, local transmission rather than importation drives the variant's growth.

## Sources

- J. Arino, P.-Y. Boëlle, E. Milliken, S. Portet, "Risk of COVID-19 variant importation – How useful are travel control measures?", Infectious Disease Modelling 6 (2021) 875, Eq. (1), Appendix A.1, Appendix B.2 (Eqs. (B.3)–(B.6)) and Sections 3.4–3.5, <https://doi.org/10.1016/j.idm.2021.06.006>, PMCID PMC8272889.
