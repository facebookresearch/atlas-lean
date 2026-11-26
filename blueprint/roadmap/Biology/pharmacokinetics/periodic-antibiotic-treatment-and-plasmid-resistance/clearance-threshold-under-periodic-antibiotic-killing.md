# Clearance threshold under periodic antibiotic killing

**Baseline model.** The bacterial load $B(t)$ grows logistically and is killed at a periodic antibiotic rate:

$$\dot B = rB\Bigl(1 - \frac{B}{K}\Bigr) - \mu(t)B ,$$

with $r, K > 0$ and $\mu$ non-negative, continuous and 1-periodic (daily dosing). Every $B(0) \ge 0$ gives a unique global non-negative solution. Define

$$\mathcal{R}_0 = e^{\,r - \int_0^1 \mu(t)\,dt}.$$

**Theorem.** If $\mathcal{R}_0 > 1$, then for every $B(0) > 0$ the solution converges to a unique non-constant, globally asymptotically stable 1-periodic solution $\Phi(t)$ (treatment failure). If $\mathcal{R}_0 < 1$, then $B \equiv 0$ is globally stable (clearance).

**Plasmid-borne resistance.** With plasmid-free $B_s$ and plasmid-bearing $B_p$, $B = B_s + B_p$, horizontal transfer at rate $\beta B_sB_p/(a + bB)$ and plasmid loss with probability $p$ at division,

$$\dot B_s = r_sB_s\Bigl(1-\tfrac{B}{K}\Bigr) - \mu_s(t)B_s - \frac{\beta B_sB_p}{a+bB} + \tfrac{p}{2}r_pB_p, \qquad \dot B_p = r_pB_p\Bigl(1-\tfrac{B}{K}\Bigr) - \mu_p(t)B_p + \frac{\beta B_sB_p}{a+bB} - \tfrac{p}{2}r_pB_p .$$

Linearizing at $(0,0)$ gives an upper-triangular periodic system whose Floquet multipliers are $\mathcal{R}_0^s = e^{\int_0^1(r_s - \mu_s)}$ and $\mathcal{R}_0^p = e^{\int_0^1(r_p(1-p/2) - \mu_p)}$; the infection-free state is locally asymptotically stable if $\max\{\mathcal{R}_0^s,\mathcal{R}_0^p\} < 1$, and globally stable if $\int_0^1(r_{\max} - \mu_{\min})\,du < 0$. If $\int_0^1(r_s - \mu_s) > 0$, a 1-periodic plasmid-free state $(B_s^*(t), 0)$ exists, stable when the corresponding invasion multipliers are below one, and under an explicit integral invasion condition for $B_p$ both strains persist uniformly.

## Expansion

The substitution $u = 1/B$ turns the periodic logistic equation into a linear equation $\dot u = -(r - \mu(t))u + r/K$, solvable in closed form. Its homogeneous part has period map multiplier $e^{-(r - \bar\mu)}$, so for $r > \bar\mu$ the affine period map is a contraction with a unique positive fixed point, the periodic orbit $\Phi$, which attracts every positive solution; for $r < \bar\mu$ the load decays to zero. Only the time-average of the killing rate enters the threshold, so protocols with the same mean exposure share the clearance criterion even though they produce different periodic loads and different selection for resistant strains.

## Sources

- A. Zhang, S. Ruan, X. Huo, "Impact of Resistance Development Mechanisms on Antibiotic Treatment Outcomes" (2025), model (M1), Proposition 2.1, Theorem 2.2, model (M2), Proposition 2.3, Theorems 2.4, 2.5 and 2.8, <https://doi.org/10.48550/arXiv.2511.03677>.
