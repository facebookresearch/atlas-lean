# Otto–Villani theorem

Let $(X, d, m)$ be a complete separable metric space with a Borel probability measure $m$ that
satisfies the [logarithmic Sobolev inequality](satisfies-log-sobolev.md) with constant
$\alpha > 0$. Then $m$ satisfies [Talagrand's inequality](satisfies-talagrand.md) with constant
$2/\alpha$:

$$W_2(\mu, m)^2 \le \frac{2}{\alpha} \operatorname{KL}(\mu \,\|\, m) \quad \text{for every probability measure } \mu.$$

Otto and Villani proved it on Riemannian manifolds using Otto's formal Riemannian calculus on the
Wasserstein space. Gigli and Ledoux present the argument as follows (their Section 3, after
Gigli, Kuwada and Ohta, who first put forward the key metric-speed bound): along the heat flow $\mu_t$ started at $\mu$, the entropy
$\varphi(t) = \operatorname{Ent}_m(\mu_t)$ has $\varphi' = -I(\mu_t)$ (the Fisher information), the
metric speed satisfies $|\dot\mu_t|^2 \le I(\mu_t)$, and the log-Sobolev inequality
$I \ge 2\alpha\varphi$ turns these into
$|\dot \mu_t| \le -\tfrac{d}{dt} \sqrt{2\varphi(t)/\alpha}$; integrating in time gives
$W_2(\mu, m) \le \sqrt{2 \operatorname{Ent}_m(\mu)/\alpha}$. Gigli and Ledoux carry this argument out on metric
measure spaces with the heat flow of the Cheeger energy.

Applied to [Gross' inequality](kl-div-with-density-std-gaussian-le.md) for the Gaussian measure
($\alpha = 1$, once extended from smooth positive densities to nonnegative Lipschitz ones) it
recovers [Talagrand's inequality for the Gaussian measure](../talagrand-std-gaussian.md).

## Sources

- N. Gigli, M. Ledoux, *From log Sobolev to Talagrand: a quick proof*, Discrete Contin. Dyn. Syst. Ser. A (2013); preprint at https://cvgmt.sns.it/paper/1689/, Theorem 5.3 and Section 3.
- N. Gigli, K. Kuwada, S. Ohta, *Heat flow on Alexandrov spaces* (cited by Gigli and Ledoux as their reference [6] for the metric-speed bound).
- F. Otto, C. Villani, *Generalization of an inequality by Talagrand and links with the logarithmic Sobolev inequality*, J. Funct. Anal. 173 (2000), 361–400.
