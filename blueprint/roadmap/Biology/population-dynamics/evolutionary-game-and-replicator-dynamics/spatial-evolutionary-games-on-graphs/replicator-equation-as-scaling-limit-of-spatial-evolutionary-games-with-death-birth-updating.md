# Replicator equation as the scaling limit of spatial evolutionary games with death-birth updating

**Model.** A population occupies the $N_n$ sites of a finite set $E_n$ carrying an irreducible reversible random-walk kernel $q^{(n)}$ with zero trace and stationary law $\pi^{(n)}$. Each site holds a strategy in a finite set $S$, and the individual at $x$ has fitness $1 - w_n + w_n\sum_y q^{(n)}(x,y)\Pi(\xi(x),\xi(y))$ for a payoff matrix $\Pi$ and selection intensity $w_n$. Under **death-birth updating**, each individual dies at rate $1$ and its neighbors compete to fill the site, reproducing with probability proportional to fitness. Mutation to $\sigma$ occurs at rate $\mu_n(\sigma)$. At $w_n = 0$ this is the voter model, so the game is a voter-model perturbation. Let $p_\sigma(\xi) = \sum_x\pi^{(n)}(x)\mathbf{1}_{\{\xi(x) = \sigma\}}$ be the strategy densities, and let $\gamma_n$ be the coalescing-lineage time scale of the voter model (of order at least $N_n$).

**Theorem.** Assume: (a) the initial densities converge in law to $\overline\nu_\infty$; (b) $0 < \liminf N_n\pi^{(n)}_{\min} \le \limsup N_n\pi^{(n)}_{\max} < \infty$; (c) three coalescence constants $\overline\kappa_{(2,3)|0}$, $\overline\kappa_{(0,3)|2}$, $\overline\kappa_{0|2|3} \ge 0$, built from meeting probabilities of ancestral lineages, exist and depend only on the spatial structure; (d) there is an admissible time change $\theta_n \to \infty$ with $\theta_n/\gamma_n \to 0$, together with mixing conditions, $\mu_n(\sigma)\theta_n \to \mu_\infty(\sigma)$, $w_n \to 0$ and $w_n\theta_n/(2\gamma_n\nu_n(\mathbf{1})) \to w_\infty$. Then:

*(1)* The density process $p(\xi_{\theta_nt})$ converges in law to the solution of the extended replicator–mutator equation

$$ \dot X_\sigma = w_\infty X_\sigma\Big(F_\sigma(X) + \widetilde F_\sigma(X) - \sum_{\sigma''}F_{\sigma''}(X)X_{\sigma''}\Big) + \mu_\infty(\sigma)(1 - X_\sigma) - \mu_\infty(S\setminus\{\sigma\})X_\sigma, $$

where $F_\sigma(X) = \overline\kappa_{0|2|3}\sum_{\sigma'}\Pi(\sigma,\sigma')X_{\sigma'}$ and

$$ \widetilde F_\sigma(X) = (\overline\kappa_{(2,3)|0} - \overline\kappa_{0|2|3})\Big(\Pi(\sigma,\sigma) - \sum_{\sigma'}\Pi(\sigma',\sigma')X_{\sigma'}\Big) + (\overline\kappa_{(0,3)|2} - \overline\kappa_{0|2|3})\sum_{\sigma'}\big[\Pi(\sigma,\sigma') - \Pi(\sigma',\sigma)\big]X_{\sigma'} , $$

with the combined constant strictly positive, so selection acts nontrivially.

*(2)* If moreover $\gamma_n\nu_n(\mathbf{1})/\theta_n \to 0$, the rescaled martingale fluctuations $(\gamma_n/\theta_n)^{1/2}M^{(n)}$ converge to a centered Gaussian martingale with Wright–Fisher covariation $\int_0^t X_\sigma(s)[\delta_{\sigma\sigma'} - X_{\sigma'}(s)]\,ds$.

**Corollary (prisoner's dilemma).** For two strategies with $\Pi = \begin{pmatrix} b - c & -c\\ b & 0\end{pmatrix}$ (cooperator $1$, defector $0$), symmetric $q^{(n)}$ and asymptotically constant two-step return probability $q^{(n),2}(x,x) \approx q^{(\infty),2}$, the cooperator density satisfies

$$ \dot X_1 = w_\infty\big(b\,q^{(\infty),2} - c\big)X_1(1 - X_1) + \mu_\infty(1)(1 - X_1) - \mu_\infty(0)X_1 . $$

Cooperation is favored iff $b\,q^{(\infty),2} > c$. On large random $k$-regular graphs $q^{(\infty),2} = 1/k$, so the condition is $b/c > k$.

## Expansion

The proof works with the semimartingale decomposition of the density process. Its drift involves densities of local patterns (pairs and triples of neighboring sites), which do not close in terms of $p$ alone. On the intermediate time scale $1 \ll \theta_n \ll \gamma_n$, the voter dynamics decorrelates these local patterns faster than the densities move. Duality with coalescing random walks then expresses the pattern frequencies through ancestral-lineage meeting probabilities, giving the constants $\overline\kappa$ and an asymptotic closure of the equations. The selection strength must be of inverse order ($1/N \ll w \ll 1$ for typical structures) so that the drift survives the time change. No local weak convergence or locally tree-like geometry is needed, which answers a pair-approximation conjecture for many non-regular graphs, up to implicit spatial constants.

## Sources

- Yu-Ting Chen, "The replicator equation in stochastic spatial evolutionary games", arXiv:2010.06025 (2020), Section 1 (model and the functions $F_\sigma$, $\widetilde F_\sigma$), Section 2, Definition 2.1, Theorem 2.2 and Corollary 2.3, <https://doi.org/10.48550/arXiv.2010.06025>.
