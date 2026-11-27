# Critical noise intensities and early escape from canards near a folded node

**Setting.** Fast–slow systems with one fast and two slow variables, $\epsilon\dot x = f(x,y,z)$, $(\dot y,\dot z) = g(x,y,z)$, model neurons and other excitable systems that show *mixed-mode oscillations* (MMOs): alternating large relaxation spikes and small-amplitude oscillations (SAOs). Near a generic *folded node* of the critical manifold the system can be brought to the normal form

$$\epsilon\dot x = y - x^2, \qquad \dot y = -(\mu+1)x - z, \qquad \dot z = \tfrac{\mu}{2},$$

with eigenvalue ratio $\mu \in (0,1)$. Deterministically (Wechselberger, Benoît, Brøns–Krupa–Wechselberger), the strong and weak singular canards perturb to maximal *primary canards*; assuming $\mu^{-1} \notin \mathbb Z$ and $\epsilon$ small, if $2k+1 < \mu^{-1} < 2k+3$ and $\mu^{-1} \ne 2(k+1)$ there are $k$ *secondary canards*, the $j$-th twisting $2j+1$ times around the weak canard within an $O(\sqrt\epsilon)$ neighborhood of the fold, and these canards organize the SAO patterns. In the rescaled variables the distance of the $k$-th secondary canard to the weak canard is $O(e^{-c_0(2k+1)^2\mu})$ as $\mu \to 0$.

The stochastic system adds independent Gaussian white noise of intensity $\sigma$ to the fast variable and $\sigma' = \rho\sigma$ to the slow variables.

**Theorem (concentration in covariance tubes).** Linearizing around a maximal canard gives a covariance matrix $V(z)$ whose diagonal entries satisfy $V_{11}, V_{22} \asymp 1/|z|$ for $z_0 + O(\mu|\log\mu|) \le z \le -\sqrt\mu$ and $\asymp 1/\sqrt\mu$ for $|z| \le \sqrt\mu$. Sample paths stay in the tube $\mathcal{B}(r) = \{\langle\zeta, V(z)^{-1}\zeta\rangle < r^2\}$ around the canard: for $\sigma < r < r_0\mu^{3/4}$,

$$\mathbb{P}\{\tau_{\mathcal{B}(r)} < z\} \le C_+(z,z_0)\,e^{-\kappa_0 r^2/(2\sigma^2)},\qquad \kappa_0 = 1 - O(\Delta) - O(r\mu^{-3/4}) - O(\sigma^2/r^2),$$

for all $z \le \sqrt\mu$.

**Corollary (noisy SAOs).** With $\sigma_k(\mu) = \mu^{1/4}e^{-c_0(2k+1)^2\mu}$, the covariance tubes around the $k$-th secondary canard and its neighbors overlap on $\{z = 0\}$ when $\sigma > \sigma_k(\mu)$: small oscillations with $2k+1$ twists become indistinguishable from noise above this critical intensity.

**Theorem (early escape).** For $z > \sqrt\mu$ the deterministic canard follows the repelling slow manifold, but sample paths leave a neighborhood $\mathcal{D}(\eta)$ of the primary canard early: whenever $\sigma|\log\sigma|^{\gamma_1} \le \mu^{3/4}$,

$$\mathbb{P}\{\tau_{\mathcal{D}(\eta)} > z\} \le C_0|\log\sigma|^{\gamma_2}\exp\Big(-\kappa\frac{z^2 - \mu}{\mu|\log\sigma|}\Big),$$

so paths typically jump away after $z$ of order $\sqrt{\mu|\log\sigma|}$, much earlier than deterministic canards, which can change the global MMO pattern.

## Expansion

Before the fold, solutions are attracted towards the slow manifold, so noise-induced deviations saturate at a level set by the linearization, giving Gaussian covariance tubes whose width grows like $\sigma|z|^{-1/2}$ and reaches $\sigma\mu^{-1/4}$ near the folded node. Since secondary canards are exponentially close to the weak canard in $(2k+1)^2\mu$, tubes overlap once $\sigma\mu^{-1/4}$ exceeds that spacing, which defines $\sigma_k(\mu)$. After the fold, the repelling dynamics amplify fluctuations exponentially at a rate proportional to $z^2/\mu$, so noise of size $\sigma$ is amplified to order one after a delay of order $\sqrt{\mu|\log\sigma|}$; this early-jump mechanism can remove SAOs or change their number in an MMO pattern.

## Sources

- Nils Berglund, Barbara Gentz and Christian Kuehn, "Hunting French ducks in a noisy environment", Journal of Differential Equations 252 (2012), 4786–4841, <https://doi.org/10.1016/j.jde.2012.01.015>; numbering as in arXiv:1011.3193: Proposition 3.1, Theorems 3.2–3.4, Theorem 4.4, Theorems 6.1–6.2, Corollary 6.3 and Theorem 6.4.
