# Queueing-theoretic reproduction number of a service facility

**Model.** Customers arrive at a service facility (a queue in steady state, with state space $\mathcal{S}$ and stationary law $\pi$). One arriving customer is infectious (the IC); all others are susceptible. By PASTA, the IC sees state $s$ with probability $\pi(s)$, with $n(s)$ other customers present. For customer $i$ present on arrival, let $W_i^{(s)} = \min(d_i,d) - a$ be the **sojourn-time overlap**, where $a$ and $d$ are the IC's arrival and departure times and $d_i$ is customer $i$'s departure. Customer $i$ is infected iff $W_i^{(s)} > \theta_i$, where the **transmission thresholds** $\theta_i$ are i.i.d. A dose–response model with constant exposure rate gives $\theta \sim \mathrm{Exp}(\alpha)$.

**Proposition (facility $R_0$).** The expected number of customers infected by one infectious customer is

$$ R_0 = 2\sum_{s\in\mathcal{S}}\pi(s)\sum_{i=1}^{n(s)}\mathbb{P}\big(W_i^{(s)} \ge \theta\big) $$

for any threshold distribution. If $\theta \sim \mathrm{Exp}(\alpha)$, then with $\widetilde W_i^{(s)}$ the Laplace transform of $W_i^{(s)}$ and $\mathbb{E}[N]$ the time-average number in system,

$$ R_0 = 2\Big(\mathbb{E}[N] - \sum_s\pi(s)\sum_{i=1}^{n(s)}\widetilde W_i^{(s)}(\alpha)\Big). $$

**Closed forms.** Let $\eta = \alpha/\mu$ be the normalized transmission rate.

*(i)* M/M/1/FCFS with load $\rho = \lambda/\mu$: $W_i^{(s)} \sim \mathrm{Erlang}(i,\mu)$, $\widetilde W_i^{(s)}(\alpha) = (1+\eta)^{-i}$, and

$$ R_0 = 2\,\frac{\rho}{1-\rho}\cdot\frac{\eta}{\eta + 1 - \rho} . $$

This is convex increasing in the arrival rate $\lambda$, convex decreasing in the service rate $\mu$, and concave increasing in $\alpha$; the same holds for the infection rate $\lambda R_0$.

*(ii)* M/M/$c$/FCFS with load $\rho = \lambda/(c\mu)$ and Erlang-C probability $C(c,\rho)$:

$$ R_0 = 2\Big(\frac{\rho}{1-\rho}C(c,\rho) + c\rho - \frac{1}{\eta+2}\Big(C(c,\rho)\,\frac{2c\rho - c\eta}{\eta + c - c\rho} + 2c\rho\Big)\Big). $$

These formulas let one compare interventions quantitatively: occupancy limits (M/M/$c$/$k$), priority or dedicated time windows for high-risk customers, and faster service. Faster service lowers both $\mathbb{E}[N]$ and the overlaps, and therefore $R_0$.

## Expansion

The IC infects customers already present (counted by the inner sum) and customers who arrive during its stay. In steady state a symmetry argument shows that the two groups contribute equally in expectation, which gives the factor $2$. With exponential thresholds, $\mathbb{P}(W \ge \theta) = 1 - \mathbb{E}e^{-\alpha W}$, so only Laplace transforms of overlaps are needed. In M/M/1/FCFS, the overlap with the $i$-th customer ahead is the time until that customer leaves, a sum of $i$ exponential service times, because that customer departs before the IC. Summing the geometric series against the geometric stationary law $\pi(s) = (1-\rho)\rho^s$ gives the closed form.

## Sources

- Kang Kang, Sherwin Doroudi, Mohammad Delasay and Alexander Wickeham, "A Queueing-Theoretic Framework for Evaluating Transmission Risks in Service Facilities During a Pandemic", arXiv:2103.13441 (2021), Section 3 (model), Section 4 (Proposition 1, Corollary 1, Propositions 2–3), Section 5 (interventions, Propositions 4–6), Appendix A (symmetry argument), <https://doi.org/10.48550/arXiv.2103.13441>.
