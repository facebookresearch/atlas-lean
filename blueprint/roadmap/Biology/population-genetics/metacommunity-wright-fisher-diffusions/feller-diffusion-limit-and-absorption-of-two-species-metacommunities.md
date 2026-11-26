# Feller diffusion limit and absorption of two-species metacommunities

**Model.** Two species $\alpha$ and $\beta$ occupy $m$ patches with capacities $N_i = \kappa_i N$, where $1 = \kappa_1 \ge \kappa_2 \ge \dots \ge \kappa_m > 0$. The state $x \in [0,1]^m$ records the frequency of species $\alpha$ in each patch. Each generation, every patch reproduces by the neutral Wright–Fisher model (binomial resampling of $N_i$ individuals), then a deterministic migration map $\Phi \colon [0,1]^m \to [0,1]^m$ redistributes individuals; the transition operator is $Pf = B_N(f \circ \Phi)$ with $B_N$ the multivariate Bernstein operator, and $X^N$ is the jump process running this chain at rate $N$, with generator $N(P - I)$. Assume:
- (conservation) $\sum_i N_i\Phi^{(i)}(x) = \sum_i N_ix_i$ for all $x$;
- (weak migration) $\sup_x |\Phi(x) - x| \to 0$ and $N(\Phi(x) - x) \to b(x)$ uniformly, for some $b \in C^2([0,1]^m, \mathbb{R}^m)$.

Let $a(x) = \mathrm{diag}\big(x_1(1-x_1)/\kappa_1, \dots, x_m(1-x_m)/\kappa_m\big)$ and
$$L = \frac12\sum_{i=1}^m a_i(x)\,\partial^2_{x_ix_i} + \sum_{i=1}^m b_i(x)\,\partial_{x_i}, \qquad \mathcal{D}(L) = C^2([0,1]^m),$$
which degenerates on the whole boundary of the cube. The states $\mathbf 0 = (0, \dots, 0)$ and $\mathbf 1 = (1, \dots, 1)$ (one species extinct everywhere) are absorbing.

**Theorem.**
1. *(Feller property.)* $L$ is closable and its closure generates a Feller semigroup $(T(t))_{t \ge 0}$ on $C([0,1]^m)$, with $C^2([0,1]^m)$ as a core.
2. *(Convergence.)* If the initial laws $\mu_N$ of $X^N$ converge weakly to $\mu$, then $X^N$ converges in distribution in the Skorokhod space $D(\mathbb{R}_+, [0,1]^m)$ to the Feller diffusion with semigroup $T$ and initial law $\mu$.
3. *(Absorption.)* If moreover $\langle b(x), n(x)\rangle > 0$ for every boundary point $x \notin \{\mathbf 0, \mathbf 1\}$, with $n(x)$ the inward normal, then from every starting point the diffusion reaches $\{\mathbf 0, \mathbf 1\}$ in finite time almost surely: one species goes globally extinct.

## Expansion

Because the diffusion matrix vanishes on every face of the cube, standard existence results for elliptic operators do not apply; the Feller semigroup is built by controlling derivatives of solutions of the backward equation for the diagonal Wright–Fisher part and perturbing by the migration drift. Conservation forces the drift to point inward, or be tangent, on the boundary, so the cube is invariant. The inward-drift condition prevents the process from being trapped on a lower-dimensional face where one species is absent only locally: migration from other patches reintroduces it, until drift and fluctuations drive the whole metacommunity to monomorphism.

## Sources

- B. Henry, C. Wang, "Feller property and absorption of diffusions for multi-species metacommunities", arXiv:2601.16616 (2026), Section 2.1 (finite population model), Section 2.2 (hypotheses on exchange transformations), Section 2.3 (Feller-property, convergence and absorption theorems), <https://doi.org/10.48550/arXiv.2601.16616>.
