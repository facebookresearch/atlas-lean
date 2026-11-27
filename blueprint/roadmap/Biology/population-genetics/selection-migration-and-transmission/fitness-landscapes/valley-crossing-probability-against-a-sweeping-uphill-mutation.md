# Valley-crossing probability against a sweeping uphill mutation

Keep the wild type $w$, uphill genotype $u$ (advantage $s_u$, mutation rate $\mu_u$), intermediate $i$ (effect $-\delta_i$, rate $\mu_i$) and double mutant $v$ (advantage $s_v$, rate $\mu_v$) of the competing-trajectories model, and let the population be large enough that $N\mu_i > 1$ and $N\mu_u > 1$. Then the numbers of intermediate and uphill mutants are well approximated by their deterministic expectations, the only randomness left being the appearance time of the first successful double mutant. With $f_u(t)$ the logistic frequency of the uphill genotype,

$$\frac{\partial f_u}{\partial t} = \mu_u (1 - f_u) + s_u f_u (1 - f_u),$$

the rate at which successful double-mutant lineages appear is $\lambda_v(t) = N f_i(t) \mu_v \pi_{iv} \approx 2 N f_i(t) \mu_v \bigl(s_v - s_u f_u(t)\bigr)$ with $f_i = f_i^{*}(1 - f_u)$, and integrating the inhomogeneous Poisson rate over the whole sweep gives

$$P_{\mathrm{cross}} = 1 - \exp\left( - \int_0^{\infty} \lambda_v(t)\, dt \right) = 1 - \exp(-2 N \Gamma), \qquad \Gamma \equiv \frac{\mu_i \mu_v s_v \gamma}{s_u},$$

where $\gamma$ is an explicit function of $s_u$, $\mu_u$, $s_v$ and $\delta_i$ with separate closed forms in the two regimes $\delta_i \ll 2\sqrt{\mu_v s_v}$ and $\delta_i \gg 2\sqrt{\mu_v s_v}$. Hence in this regime $P_{\mathrm{cross}}$ **increases** with $N$ and tends to one: sufficiently large populations always cross the valley rather than taking the immediately beneficial path, and inverting the expression gives the size $N = -\log(1 - P_{\mathrm{cross}})/(2\Gamma)$ at which a given crossing probability is reached.

At intermediate sizes, where the Poisson approximation for the appearance of intermediate lineages still holds, the crossing probability instead splits as $P_{\mathrm{cross}} = P_{v,1} + (1 - P_{v,1}) P_{v,2}$, with $P_{v,1}$ the probability that a successful valley-crossing lineage appears before the uphill mutant establishes — a race between two exponential clocks of rates $\lambda_v = N\mu_i p_v$ and $\lambda_u = N \mu_u \pi_{wu} \approx 2 N \mu_u s_u$, offset by the delay $\Delta\tau = \tau_{\mathrm{drift}} - \tau_{\mathrm{est}}$:

$$P_{v,1} = \begin{cases} \dfrac{\lambda_v}{\lambda_v + \lambda_u} e^{-\lambda_u \Delta\tau}, & \Delta\tau > 0, \\[6pt] 1 - \dfrac{\lambda_u}{\lambda_v + \lambda_u} e^{-\lambda_v \Delta\tau}, & \Delta\tau < 0. \end{cases}$$

## Depends on

- [Greedy adaptation versus valley crossing in the sequential-fixation regime](greedy-adaptation-versus-valley-crossing-in-the-sequential-fixation-regime.md)
- [Logistic trajectory of a selective sweep](../../../detecting-selection/selective-sweeps/sweep-traj.md)
- [Inhomogeneous Poisson processes by a deterministic time change](../../../../Probability/point-processes/poisson-processes/inhomogeneous-poisson-processes-by-deterministic.md)

## Expansion

The sweeping uphill mutation acts on the valley-crossing lineage in three ways, all captured by replacing the constant parameters with time-dependent effective ones: the wild-type background on which intermediates arise shrinks as $N_{\mathrm{wt}}(t) = N(1 - f_u)$, the intermediate becomes effectively more deleterious, with effective effect $-\delta_i - f_u s_u$ (deleteriousness $\delta_i + f_u s_u$), and the double mutant becomes effectively less beneficial, $s_{v,\mathrm{eff}} = s_v - f_u s_u$. Substituting the logistic $f_u$ and integrating over the sweep is what produces $\gamma$ and hence $\Gamma$. Taken together with the sequential-fixation result, the dependence of $P_{\mathrm{cross}}$ on $N$ is nonmonotone: it falls through the sequential-fixation regime, reaches a minimum inside the stochastic-tunneling regime (it does not rise at once at the onset of tunneling), and rises back to one in the deterministic regime. The stochastic-tunneling formula of the intermediate regime assumes $\delta_i$ effectively constant over the drift time, which holds when $s_u \ll 2\sqrt{2/\log 2}\sqrt{\mu_v s_v}$ (for $\delta_i \ll 2\sqrt{\mu_v s_v}$) or $s_u \ll 2\delta_i$ (for $\delta_i \gg 2\sqrt{\mu_v s_v}$); under these conditions the uphill mutation still enters that formula.

## Sources

- I. E. Ochs, M. M. Desai, "The competition between simple and complex evolutionary trajectories in asexual populations", *BMC Evolutionary Biology* 15 (2015), 55, <https://doi.org/10.1186/s12862-015-0334-0> (PMC4391547). Results, "Stochastic tunneling" and the large-population regime, Equations (13)–(34).
