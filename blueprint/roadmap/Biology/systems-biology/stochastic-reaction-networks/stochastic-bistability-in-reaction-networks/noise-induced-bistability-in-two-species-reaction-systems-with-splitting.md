# Noise-induced bistability in two-species reaction systems with splitting

**Setting.** A closed system holds $N$ molecules of two species, and $X_A\in\{0,\dots,N\}$ counts the first species. Two mechanisms act. *Chemical reactions* of type $(a,b,\zeta)$ consume $a$ molecules of the first species and $b$ of the second and change $X_A$ by $\zeta$; they have mass-action rates $\kappa^{ab}_\zeta=\tilde\kappa^{ab}_\zeta N^{1-(a+b)}$. *Splitting/resampling* events make unbiased changes to $X_A$ at rate $\varepsilon^2\gamma(x,N)$, with local variance $\tilde\gamma^2\tilde\sigma^2(x)$ that vanishes at $x=0,1$. Write $X_N=X_A/N$. At least one reaction escapes each boundary, so $\tilde\phi(0)>0>\tilde\phi(1)$ for the limiting drift $\tilde\phi(x)=\sum\zeta\,\tilde\kappa^{ab}_{\zeta,\mu}x^a(1-x)^b$.

**Theorem (slow splitting: metastable interior wells).** Suppose the splitting strength $\varepsilon_A$ is finite. Then $X_N\Rightarrow\tilde X$ in Skorokhod space, where $\tilde X$ is a diffusion on $[0,1]$ with drift $\tilde\phi$ and diffusion coefficient $\sum\zeta^2\tilde\kappa^{ab}_{\zeta,\sigma^2}x^a(1-x)^b+\tilde\gamma^2\tilde\sigma^2(x)$. Suppose further that $\tilde\phi$ has zeros $0<x_1<x_2<x_3<1$, with $x_1,x_3$ stable, so the potential is a double well. Then for the small-noise diffusion $\tilde X_\varepsilon$:

- the exit time from the well of $x_3$, rescaled by its mean $\beta_\varepsilon$, is asymptotically $\mathrm{Exp}(1)$;
- $\varepsilon^2\log\beta_\varepsilon\to I_{x_3,x_2}$, the Freidlin–Wentzell quasipotential barrier;
- the occupation measure converges to a two-state jump process between $\delta_{x_1}$ and $\delta_{x_3}$.

For birth–death chains with $r_\pm(Nx)/N\to\tilde r_\pm(x)$, the transition times instead satisfy $\frac1N\log\beta_N\to\imath_{x_3,x_2}(\tilde r_+,\tilde r_-)$, with the discrete quasipotential $\imath$. When $N\varepsilon_N^2\to1$ this discrete rate is the correct one and is more informative than the diffusion rate.

**Theorem (fast splitting: boundary bistability).** Suppose the reaction rates on the boundary are of order $\omega_N\to\infty$ and, for a time scale $\beta_N$, the escape and crossing probabilities satisfy

$$\tfrac{1}{\omega_N}\textstyle\sum_j r_{0j}\to\tilde r_+,\quad \tfrac1{\omega_N}\sum_j r_{Nj}\to\tilde r_-,\quad \beta_N\sum_j r_{0j}\pi_{jN}\to\tilde r_{01},\quad \beta_N\sum_j r_{Nj}\pi_{j0}\to\tilde r_{10},$$

together with vanishing mean excursion times. Then the times between switches, measured in units of $\beta_N$, converge to $\mathrm{Exp}(\tilde r_{01})$ and $\mathrm{Exp}(\tilde r_{10})$. The occupation measure of $X_N$ converges to the jump process alternating between $\delta_0$ and $\delta_1$. For a birth–death chain with $r_+(0)/N\to\tilde r_+$, $r_-(N)/N\to\tilde r_-$, $\sum_i|\varepsilon_N(i)|\to0$, $\sum_i (N-i)/r_+(i)\to0$ and $\sum_i i/r_-(i)\to0$, these conditions hold with $\omega_N=N$, $\beta_N=1$, $\tilde r_{01}=\tilde r_+$ and $\tilde r_{10}=\tilde r_-$.

## Proof sketch

In the slow-splitting regime the drift dominates, and bistability is the classical metastability of a double-well diffusion. Switching is exponentially rare, and Kramers/Freidlin–Wentzell theory gives the rates. In the fast-splitting regime the unbiased noise swamps the drift in the interior, so $X_N$ is nearly a martingale and is pushed against the boundaries, which absorb the noise because $\tilde\sigma^2$ vanishes there. Only the biased reactions at $0$ and $1$ start excursions. A martingale started next to $0$ reaches $1$ before returning with probability about $1/N$, so the escape rate $\sim N$ times the crossing probability $\sim 1/N$ gives switching on an $O(1)$ time scale. The resulting bistability between the two pure states comes from the noise alone: the deterministic drift may have a single interior stable point.

## Sources

- John K. McSweeney and Lea Popovic, "Stochastically-induced bistability in chemical reaction systems", *The Annals of Applied Probability* 24 (2014), 1226–1268, <https://doi.org/10.1214/13-aap946>. Preprint version: arXiv:1302.1446 (2013), Section 2 (diffusion limit of the rescaled process), Section 3 "Bistable behavior from slow splitting" (exponential exit law, quasipotential asymptotics, metastable jump-process limit, birth–death large deviations and their comparison with the small-noise diffusion), Section 4 "Bistable behavior from fast splitting" (boundary switching limit and birth–death sufficient conditions), <https://doi.org/10.48550/arXiv.1302.1446>.
