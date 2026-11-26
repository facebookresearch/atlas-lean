# Wasserstein contraction of bursty gene regulatory network models

**Model.** For $n$ genes, protein levels $X = (X_1, \dots, X_n)$ follow a piecewise-deterministic Markov process: between jumps $X_i' = -d_{1,i} X_i$, and gene $i$ fires a burst at rate $k_{\mathrm{on},i}(X)$, adding an $\mathrm{Exp}(1)$-distributed amount to $X_i$ (protein-only model). In the mRNA–protein model, mRNA $Y_i$ jumps by exponential bursts at rate $k_{\mathrm{on},i}(Z)$, decays at rate $d_{0,i}$, and proteins follow $Z_i' = d_{1,i}(Y_i - Z_i)$. Assume each rate decomposes as $k_{\mathrm{on},i}(x) = k_{0,i} + (k_{1,i} - k_{0,i})\,\phi_i(x)$ with $\phi_i : \mathbb R^n \to [0,1]$ being $\ell_i$-Lipschitz, and set

$$r = \sum_i (k_{1,i} - k_{0,i}), \qquad L = \frac{1}{r}\sum_i \ell_i, \qquad d_1 = \min_i d_{1,i}, \qquad \kappa = \frac{r}{d_1}, \qquad \tau = r \wedge d_1,$$

so that $\|k_{\mathrm{on}}(x) - k_{\mathrm{on}}(z)\| \le r(1 \wedge L\|x - z\|)$. For $u \ge 0$ let

$$p^*(u) = e^{-\kappa(1 \wedge L(u \vee \kappa))} \bigl(1 \vee L(u \vee \kappa)\bigr)^{-\kappa}.$$

**Theorem.** For two initial laws $\mu^1(0), \mu^2(0)$ of the protein-only model with $W_1(0) = W_1(\mu^1(0), \mu^2(0))$ and $p^* = p^*(W_1(0))$, for all $t \ge 0$

$$W_1(\mu^1(t), \mu^2(t)) \le \Bigl(W_1(0) \vee \kappa + \gamma e^{-1}\bigl(W_1(0) + \tau(1 - p^*)\bigr) t\Bigr) e^{-\gamma t}, \qquad \gamma = \frac{p^* \tau d_1}{p^* \tau + d_1}.$$

Consequently the model has a unique stationary distribution $\mu_\infty$, approached at this explicit exponential rate. The analogous bound holds for the protein coordinate of the mRNA–protein model (with a weighted Wasserstein distance on the mRNA initial laws), which also has a unique stationary protein distribution. No smallness condition on the interaction strength $L$ and no positive lower bound on $k_{\mathrm{on}}$ is required.

## Expansion

The proof couples two copies of the process so that they share bursts whenever possible; a companion process $U(t)$ dominates their distance, decays deterministically at rate at least $d_1$ and jumps only when the two burst rates disagree, which happens at rate at most $r(1 \wedge L U)$. The companion has $\mathbb E[U(t)] \le \mathbb E[U(0)] \vee \kappa$, makes almost surely finitely many jumps, and its number of jumps is stochastically smaller than a geometric variable with parameter $p^*$. Waiting times between jumps are controlled by rate $\tau$, and combining the geometric number of jumps with exponential decay gives the rate $\gamma$.

## Sources

- M. Gaillard, U. Herbach, "Quantitative ergodicity for gene regulatory networks with transcriptional bursting", arXiv:2605.08345 (2026), Theorems 2.2 and 2.3, Corollaries 2.4 and 2.5, Propositions 5.3, 5.4, 5.5 and 5.6, <https://doi.org/10.48550/arXiv.2605.08345>.
