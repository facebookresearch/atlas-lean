# Optimal timing of mass drug administration under cyclic forest migration

**Setting.** A three-scale model of *Plasmodium vivax* transmission couples within-host hypnozoite dynamics, human infection compartments and mosquito populations on two patches: a village (patch 1) and a forest (patch 2). Humans split into a stationary fraction $N$ and a moving fraction $M = 1 - N$ of forest-goers; the fractions of moving individuals on the two patches are

$$A_1(t) = u + v\cos(\omega t), \qquad A_2(t) = 1 - u - v\cos(\omega t),$$

with $0.5 \le u < 1 - v$ (mean share of time moving individuals spend in the village), small amplitude $v$, and travel frequency $\omega/2\pi$. Mosquito-to-human ratios are $Q_1, Q_2$ with $Q_1 \ll 1$. Each moving individual $j$ has a periodic movement function $B_j(t)\in\{0,1\}$ ($1$ while in the village), and these are shifted copies of one another: $B_j(t) = B_i(t + w_{ij}(t))$ with offsets $|w_{ij}| \ll 1$, so that their average is $A_1$. The force of infection on patch $i$ (infecting bites per person per day) is

$$\lambda_1(t) = \frac{ab\,I_{m1}(t)}{N + (u + v\cos\omega t)M}, \qquad \lambda_2(t) = \frac{ab\,I_{m2}(t)}{M\big((1-u) - v\cos\omega t\big)},$$

with mean bite rate $a$ per mosquito, mosquito-to-human transmission probability $b$ and infectious mosquito densities $I_{mi}$, and the hypnozoite kernel is

$$f(t) = \frac{1 - e^{-\gamma t}}{1 + \nu p_A(t)} - 1 \in [-1, 0),$$

where $\nu$ is the mean number of hypnozoites established per infective bite, $\gamma$ the clearance rate of a blood-stage infection, and $p_A(t) = \frac{\alpha}{\alpha + \mu - \gamma}\big(e^{-\gamma t} - e^{-(\alpha + \mu)t}\big)$ the probability that a hypnozoite established at time $0$ is in the activated state $A$ at time $t$ (activation rate $\alpha$, hypnozoite death rate $\mu$). On the limit cycle the infectious mosquito proportions on patch $i$ are approximated by first-order Fourier series $I^*_{mi}(t) \approx w^{(i)}_{-1}e^{-\mathrm{i}\omega t} + w^{(i)}_0 + w^{(i)}_1e^{\mathrm{i}\omega t}$.

**Theorem (moving-population prevalence).** For small $Q_1$, $|v|$ and $\sup_{i,j}|w_{ij}|$, large $\omega$, and $|f(t)| < 1$, the infectious moving population satisfies

$$I_M(t) = M - \frac{M}{1+\epsilon}\exp\left(\int_0^t\big[A_1(\tau)\lambda_1(\tau) + A_2(\tau)\lambda_2(\tau)\big]f(t-\tau)\,d\tau\right), \qquad |\epsilon| \ll 1 .$$

**Theorem (optimal annual MDA time).** Let $\tilde I_M(t,s)$ be the infectious moving proportion at time $t$ after a single mass drug administration at time $s$ with efficacies $p_{\mathrm{blood}}, p_{\mathrm{rad}}$ (against blood-stage parasites and hypnozoites), and let

$$AP(s) = \int_0^{2\pi/\omega}\tilde I_M(s+k, s)\,dk$$

be the aggregate prevalence over the first cycle after treatment, for $s \in [T, T + 2\pi/\omega]$ with $T \gg 1$ the start of a movement period. Write $S = Mu\,(w^{(1)}_{-1} + w^{(1)}_1) + (N + Mu)(w^{(2)}_{-1} + w^{(2)}_1)$ and $D = Mu\,(w^{(1)}_1 - w^{(1)}_{-1}) + (N + Mu)(w^{(2)}_1 - w^{(2)}_{-1})$. For $\omega$ large and $p_{\mathrm{blood}}, p_{\mathrm{rad}}$ close to $1$, the time $s$ minimizing $AP(s)$ is the unique $s$ with $s - T \in [0, 2\pi/\omega)$ such that

$$\tan\big(\omega(s - T)\big) = -\frac{S}{\mathrm{i}D}$$

and the constraint (29) of the source holds,

$$-S\sin\big(\omega(s-T)\big) + \mathrm{i}\big[Mu\,(w^{(1)}_1 - w^{(1)}_{-1}) - (N + Mu)(w^{(2)}_1 - w^{(2)}_{-1})\big]\cos\big(\omega(s-T)\big) < 0 .$$

Without the constraint the tangent equation has two solutions per period, one for the maximum and one for the minimum. (The source prints a minus sign before the second term in the bracket of (29), where $D$ has a plus sign.) The optimum therefore depends on demography ($M$, $N$, $u$) and on the phase of seasonal mosquito infectivity. In the source's numerical study, with parameters fitted to Vietnamese surveillance data (2011–2015), it moves toward the onset of forest travel as the moving fraction grows and falls about two days before the average departure to the forest; these are numerical observations, not part of the theorem.

## Expansion

When infection pressure is small, the probability that a moving individual remains uninfected is an exponential of the accumulated, hypnozoite-weighted force of infection along their trajectory between patches, which gives the formula for $I_M$. Treating at time $s$ removes infections in proportion to the instantaneous human reservoir; with first-order Fourier approximations, the averaged post-treatment infectivity is a sinusoid in $\omega(s - T)$ whose stationary points solve the stated tangent equation, and the sign constraint selects the minimum. The weights $Mu$ and $N + Mu$ come from how the stationary and moving populations sample the two mosquito populations.

## Sources

- S. Elgart, M. B. Flegg and J. A. Flegg, "Evaluating interventions for Plasmodium vivax forest malaria using a three-scale mathematical model", *SIAM Journal on Applied Mathematics* 86(5) (2026), 2472–2505, Section 2 (kernel $f$, movement functions $B_j$ and offsets $w_{ij}$, forces of infection), Theorems 2.1, 2.3 and 4.1 with Eqs. (27)–(29), <https://doi.org/10.1137/25m1763718> (preprint arXiv:2506.10040).
