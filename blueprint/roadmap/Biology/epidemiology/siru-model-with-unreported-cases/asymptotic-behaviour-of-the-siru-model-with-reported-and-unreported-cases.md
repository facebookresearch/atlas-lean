# Asymptotic behaviour of the SIRU model with reported and unreported cases

**Model (Liu–Magal–Seydi–Webb).** Let $S$ be susceptibles, $I$ asymptomatic infectious individuals in incubation, $R$ reported (and then isolated) infectious cases and $U$ unreported infectious cases. With transmission rate $\tau$, exit rate $\nu=\nu_1+\nu_2$ from $I$ split into a reported fraction $\nu_1/\nu$ and an unreported fraction $\nu_2/\nu$, and removal rate $\eta$ from $R$ and $U$:

$$
S'=-\tau S(I+U),\qquad I'=\tau S(I+U)-\nu I,\qquad R'=\nu_1I-\eta R,\qquad U'=\nu_2I-\eta U .
$$

Reported cases do not transmit; unreported ones do.

**Theorem.** Assume an epidemic situation $\tau S_0-\nu>0$ and initial data $S_0>0$, $I_0>0$, $R_0=0$, $U_0=\nu_2I_0/(\eta+\chi_2)$ for some $\chi_2>0$ (the exponential-phase calibration). Then:

1. $S,I,R,U$ exist for all $t>0$, are positive, and stay strictly below the total $P=S_0+I_0+U_0$;
2. $S(t)\to S_\infty>0$, while $I,R,U\to0$;
3. $R(t)/U(t)\to\nu_1/\nu_2$ from below.

Moreover $R$ and $U$ decay more slowly than $e^{-\eta t}$, and, unlike the SIR model, the curves of cases need not have a single peak.

## Depends on

- [Kermack–McKendrick SIR model](../kermack-mckendrick-sir-model/README.md)

## Expansion

Positivity and the positive limit of $S$ follow from monotonicity of $S$ and integrability of $I+U$; a closed final-size relation is not available because $S'$ depends on both $I$ and $U$, so robust integral estimates replace it. For the ratio, the last two equations give $(R'+\eta R)/\nu_1=I=(U'+\eta U)/\nu_2$, i.e. $\nu_2(Re^{\eta t})'=\nu_1(Ue^{\eta t})'$, hence

$$
\frac RU=\frac{\nu_1}{\nu_2}-\frac{\nu_1U_0}{\nu_2\,Ue^{\eta t}} .
$$

Since $R/U\to\nu_1/\nu_2$, necessarily $Ue^{\eta t}\to\infty$, which is the slower-than-$e^{-\eta t}$ decay, and the correction term is negative, which gives convergence from below. The reported-to-unreported ratio thus increases during the epidemic: the proportion of unreported cases is largest early on, which matters when testing capacity is low. Double peaks of $R$ or $U$ can be produced by prescribing a local minimum $R'(t_p)=0$, $R''(t_p)>0$ at an intermediate time and integrating in both time directions.

## Sources

- Andrés Navas, Gastón Vergara-Hermosilla, "On the dynamics of the Coronavirus epidemic and the unreported cases: the Chilean case", arXiv:2006.02632 (2020), Section 2: model (Liu, Magal, Seydi, Webb), Theorem 2.1 and Remarks 2.2–2.6, <https://doi.org/10.48550/arXiv.2006.02632>.
