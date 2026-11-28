# Many-to-one formula for colonial branching diffusions

**Model.** A population at time $t$ consists of colonies with labels $u\in\mathbb{G}(t)$ (Ulam-Harris-Neveu labels) and resources $X^u_t>0$; write $\nu_t=\sum_{u\in\mathbb{G}(t)}\delta_{X^u_t}$, $N_t=|\mathbb{G}(t)|$ and $R_t=\langle \nu_t,\mathrm{id}\rangle=\sum_u X^u_t$. Fix $a>0$, $\mu>0$, $\lambda>0$, $\sigma>0$, $\delta>0$ and a law $q$ on $[0,1]$.

- Each colony dies at rate $\mu$.
- A colony of resource $x$ splits at rate $\lambda x/R_t$ (competition for resources acts on fission, not on death); the new colony receives $\Theta x$ and the parent keeps $(1-\Theta)x$, with $\Theta\sim q$ drawn independently.
- Between branching events,

$$\mathrm{d}X^u_t = aX^u_t\,\mathrm{d}t + \frac{\sigma}{\sqrt{1+\delta^2}}X^u_t\left(\mathrm{d}B^u_t + \delta\,\mathrm{d}W_t\right),$$

with independent intrinsic Brownian motions $B^u$ and one environmental Brownian motion $W$ shared by all colonies.

**Spinal process.** One colony, the spine, is distinguished. It is chosen initially with probability $X^j_0/R_0$, and at its own fission the new spine is the child $i\in\{1,2\}$ with probability proportional to its resource. Splitting happens at the same rate $\lambda x/\widehat R_t$; non-spinal colonies die at rate $\mu$, the spine never dies. Between events the spine and the other colonies follow

$$\mathrm{d}\widehat Y_t=(a+\sigma^2)\widehat Y_t\,\mathrm{d}t+\tfrac{\sigma}{\sqrt{1+\delta^2}}\widehat Y_t(\mathrm{d}\widehat B^*_t+\delta\,\mathrm{d}\widehat W_t),\qquad \mathrm{d}\widehat X^u_t=\Big(a+\sigma^2\tfrac{\delta^2}{1+\delta^2}\Big)\widehat X^u_t\,\mathrm{d}t+\tfrac{\sigma}{\sqrt{1+\delta^2}}\widehat X^u_t(\mathrm{d}\widehat B^u_t+\delta\,\mathrm{d}\widehat W_t).$$

Let $\widehat N_t$ be the number of colonies in the spinal population $\widehat\nu_t$.

**Theorem (sampling a uniform colony).** For $U_t$ uniform on $\mathbb{G}(t)$ and every measurable $F$ on cadlag trajectories,

$$\mathbb{E}_{\nu_0}\!\left[\mathbf 1_{\{\mathbb{G}(t)\neq\emptyset\}}F\big(X^{U_t}_t,(\nu_s)_{s\le t}\big)\right]=R_0e^{(a-\mu)t}\,\mathbb{E}_{\nu_0}\!\left[\frac{1}{\widehat Y_t\widehat N_t}F\big(\widehat Y_t,(\widehat\nu_s)_{s\le t}\big)\right].$$

**Corollary (many-to-one).** For every measurable $f$ on trajectories,

$$\mathbb{E}_{\nu_0}\!\left[\mathbf 1_{\{\mathbb{G}(t)\neq\emptyset\}}\sum_{u\in\mathbb{G}(t)}f\big((X^u_s,\nu_s)_{s\le t}\big)\right]=R_0e^{(a-\mu)t}\,\mathbb{E}_{\nu_0}\!\left[\frac{f\big((\widehat Y_s,\widehat\nu_s)_{s\le t}\big)}{\widehat Y_t}\right].$$

## Expansion

The spine is a $\psi$-spine with weight $\psi(x,\nu)=x$: the change of measure is the Girsanov-type martingale built from $x\mapsto x$, which is an eigenfunction of the branching generator with eigenvalue $a-\mu$ because fission conserves resources ($\Theta x+(1-\Theta)x=x$) and the total fission rate $\sum_u\lambda X^u/R=\lambda$ does not depend on the configuration. The size-biased choice of the spine at birth and at fission and the extra drifts ($\sigma^2$ for the spine, $\sigma^2\delta^2/(1+\delta^2)$ for the others through the shared noise) are exactly the Doob transform of that martingale. Dividing by $\widehat Y_t$ undoes the size bias, and dividing by $\widehat N_t$ turns a sum over colonies into a uniform pick. The formula reduces questions about a typical colony in an interacting population to a single tagged trajectory, which also gives a low-variance Monte Carlo estimator.

## Sources

- Sylvain Billiard, Charles Medous, Charline Smadi, "Spinal study of a population model for colonial species with interactions and environmental noise", *Stochastic Processes and their Applications* 196 (2026), 104923, Theorem 2.1 and Corollary 2.2 (Section 2.2); general $\psi$-spine construction in Theorem 3.4, <https://doi.org/10.1016/j.spa.2026.104923> (preprint arXiv:2501.17608).
