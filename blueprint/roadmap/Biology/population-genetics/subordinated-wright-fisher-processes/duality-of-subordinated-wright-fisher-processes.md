# Duality of subordinated Wright–Fisher processes

**Time change preserves duality.** Let $X$ and $Z$ be Feller Markov processes on $E$ and $F$, dual with respect to $h:E\times F\to\mathbb{R}$, i.e. $\mathbb{E}_x[h(X(t),z)]=\mathbb{E}_z[h(x,Z(t))]$ for all $t,x,z$. If $C$ is a non-decreasing clock independent of both, then $X\circ C$ and $Z\circ C$ are dual with respect to the same $h$.

**Wright–Fisher case.** For the neutral $K$-type Wright–Fisher diffusion with parent-independent mutation $\theta$, the function

$$g(x,\mathbf{m})=\frac{(|\theta|)_{(|\mathbf{m}|)}}{\prod_i(\theta_i)_{(m_i)}}\prod_{i=1}^Kx_i^{m_i}$$

(the posterior-to-prior Dirichlet density ratio after observing multinomial counts $\mathbf{m}$) gives duality with the multitype pure-death process $Z$ on $\mathbb{Z}_+^K$ jumping $\mathbf{m}\to\mathbf{m}-\mathbf{e}_i$ at rate $\lambda_{|\mathbf{m}|}m_i/|\mathbf{m}|$, $\lambda_n=n(n+|\theta|-1)/2$; it counts surviving non-mutant lines of descent of each type in a sample.

**Theorem.** Let $\widetilde X=X\circ C$ be a subordinated Wright–Fisher process with clock Laplace transform $\Phi_t(\lambda)=\mathbb{E}[e^{-\lambda C(t)}]$, and $\widetilde Z=Z\circ C$ its dual with respect to $g$. Then $\widetilde Z$ is a non-increasing pure-jump process on $\mathbb{Z}_+^K$; its time marginals are a total-count law $\widetilde q_{|\mathbf{m}|,\cdot}(t)$ (alternating series in $\Phi_t(\lambda_j)$, as for the Wright–Fisher death process with $e^{-\lambda_jt}$ replaced by $\Phi_t(\lambda_j)$) composed with hypergeometric thinning of the types, and

$$\mathbb{P}[\widetilde Z(t)=\mathbf{n}\mid\widetilde Z(0)=\mathbf{n}]=\Phi_t(\lambda_{|\mathbf{n}|}).$$

1. If $C=S$ is a subordinator with drift $\beta$ and Lévy measure $\pi$, $\widetilde Z$ is Markov, jumping from $\mathbf{n}$ to any $\mathbf{k}\le\mathbf{n}$ (hypergeometrically in the types), with total-count rates that are alternating combinations of

$$\widetilde\lambda_j=\beta\lambda_j+\int_{(0,\infty)}\big(1-e^{-u\lambda_j}\big)\pi(du),$$

so several lineages can be lost at once.
2. If $C=R$ is the inverse of a subordinator, $\widetilde Z$ is non-Markov and, after a non-exponential holding time, descends almost surely through unit jumps only: under the generalized Caputo derivative $I^{(\beta,\pi)}_t$, the initial rates are $\lambda_{|\mathbf{n}|}n_i/|\mathbf{n}|$ for $\mathbf{n}\to\mathbf{n}-\mathbf{e}_i$, exactly those of the Wright–Fisher dual.

## Depends on

- [Transition function of a subordinated Wright–Fisher process](transition-function-of-a-subordinated-wright-fisher-process.md)

## Expansion

For a fixed time, condition on $C(t)=u$: by independence, $\mathbb{E}_x[h(X(C(t)),z)]=\mathbb{E}\big[\mathbb{E}_x[h(X(u),z)]|_{u=C(t)}\big]=\mathbb{E}\big[\mathbb{E}_z[h(x,Z(u))]|_{u=C(t)}\big]=\mathbb{E}_z[h(x,Z(C(t)))]$. In the Wright–Fisher case, the total number of dual lineages is an autonomous death process whose survival probability in state $n$ over time $u$ is $e^{-\lambda_nu}$; averaging over $u=C(t)$ gives $\Phi_t(\lambda_n)$. A subordinator clock can skip over several death epochs in one jump, producing multiple losses with rates given by the Lévy–Khintchine exponent evaluated along the death rates; an inverse subordinator is continuous, so it only slows the death process down, with long pauses that encode memory. The duality is what makes posterior updating for partially exchangeable data computable: observing counts moves the dual up, and propagating in time moves it down.

## Sources

- N. A. Judd, D. Spanò, "Subordinated Wright-Fisher Priors", arXiv:2604.11363 (2026), Section 2.1, Propositions 4 and 5 and Remark following Proposition 4 (Section 3.4). <https://doi.org/10.48550/arXiv.2604.11363>
