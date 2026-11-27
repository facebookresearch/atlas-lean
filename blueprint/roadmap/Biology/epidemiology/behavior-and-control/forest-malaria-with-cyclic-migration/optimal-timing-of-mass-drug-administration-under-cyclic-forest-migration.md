# Optimal timing of mass drug administration under cyclic forest migration

**Setting.** A three-scale model of *Plasmodium vivax* transmission couples within-host hypnozoite dynamics, human infection compartments and mosquito populations on two patches: a village (patch 1) and a forest (patch 2). Humans split into a stationary fraction $N$ and a moving fraction $M = 1 - N$ of forest-goers; the fractions of moving individuals on the two patches are

$$A_1(t) = u + v\cos(\omega t), \qquad A_2(t) = 1 - u - v\cos(\omega t),$$

with $0.5 \le u < 1 - v$ (mean share of time moving individuals spend in the village), small amplitude $v$, and travel frequency $\omega/2\pi$. Mosquito-to-human ratios are $Q_1, Q_2$ with $Q_1 \ll 1$. On the limit cycle the infectious mosquito proportions on patch $i$ are approximated by first-order Fourier series $I^*_{mi}(t) \approx w^{(i)}_{-1}e^{-i\omega t} + w^{(i)}_0 + w^{(i)}_1e^{i\omega t}$.

**Theorem (moving-population prevalence).** For small $Q_1$, $|v|$ and $\sup_{i,j}|w_{i,j}|$ (the model's patch-coupling coefficients), large $\omega$, and $|f(t)| < 1$ for the hypnozoite kernel $f$, the infectious moving population satisfies

$$I_M(t) \approx M - M\exp\left(\int_0^t\big[A_1(\tau)\lambda_1(\tau) + A_2(\tau)\lambda_2(\tau)\big]f(t-\tau)\,d\tau\right),$$

with $\lambda_i$ the force of infection on patch $i$ (up to a factor $1/(1+\epsilon)$, $|\epsilon| \ll 1$).

**Theorem (optimal annual MDA time).** For $\omega$ large and treatment efficacies $p_{\mathrm{blood}}, p_{\mathrm{rad}}$ (against blood-stage parasites and hypnozoites) close to $1$, the time $s$ of a single annual mass drug administration that best reduces transmission, measured from the start $T$ of the movement period, is the unique $s - T \in [0, 2\pi/\omega)$ with

$$\tan\big(\omega(s - T)\big) = -\frac{Mu\,(w^{(1)}_{-1} + w^{(1)}_1) + (N + Mu)(w^{(2)}_{-1} + w^{(2)}_1)}{\mathrm{i}\big[Mu\,(w^{(1)}_1 - w^{(1)}_{-1}) + (N + Mu)(w^{(2)}_1 - w^{(2)}_{-1})\big]}$$

that also satisfies the second-order (minimization) sign constraint. The optimum therefore depends on demography ($M$, $N$, $u$) and on the phase of seasonal mosquito infectivity, and moves toward the onset of forest travel as the moving fraction grows; for the parameters fitted to Vietnamese surveillance data (2011–2015) it falls about two days before the average departure to the forest.

## Expansion

When infection pressure is small, the probability that a moving individual remains uninfected is an exponential of the accumulated, hypnozoite-weighted force of infection along their trajectory between patches, which gives the formula for $I_M$. Treating at time $s$ removes infections in proportion to the instantaneous human reservoir; with first-order Fourier approximations, the averaged post-treatment infectivity is a sinusoid in $\omega(s - T)$ whose stationary points solve the stated tangent equation, and the sign constraint selects the minimum. The weights $Mu$ and $N + Mu$ come from how the stationary and moving populations sample the two mosquito populations.

## Sources

- S. Elgart, M. B. Flegg and J. A. Flegg, "Evaluating interventions for Plasmodium vivax forest malaria using a three-scale mathematical model", *SIAM Journal on Applied Mathematics* 86(5) (2026), 2472–2505, Section 2 (movement functions), Theorems 2.1, 2.3 and 4.1, <https://doi.org/10.1137/25m1763718> (preprint arXiv:2506.10040).
