# Solution of the recombination equation via the partitioning process

**Setting.** Let $S = \{1, \dots, n\}$ be a set of sites with finite allele sets $X_i$, type space $X = X_1 \times \dots \times X_n$, and $\boldsymbol{P}(X)$ the probability measures on $X$. For $\varnothing \ne I \subseteq S$ let $\omega^I = \omega \circ \pi_I^{-1}$ be the marginal of $\omega$ on the sites in $I$. For a partition $\mathcal{A} = \{A_1, \dots, A_m\}$ of $S$ the *recombinator* is

$$R_{\mathcal{A}}(\omega) = \bigotimes_{A \in \mathcal{A}} \omega^A \qquad (\omega \in \boldsymbol{P}(X)),$$

the product of the marginals on the blocks (so $R_{\{S\}}(\omega) = \omega$). With rates $\varrho(\mathcal{A}) \ge 0$ for partitions $\mathcal{A}$ of $S$ into at most two blocks (two parents), the deterministic recombination equation for the type distribution of an infinite population is

$$\dot\omega_t = \sum_{\mathcal{A}} \varrho(\mathcal{A}) \big(R_{\mathcal{A}}(\omega_t) - \omega_t\big).$$

It is the large-population limit (dynamical law of large numbers) of the Moran model with recombination.

**Partitioning process.** For $U \subseteq S$ and a partition $\mathcal{B}$ of $U$ into at most two blocks let $\varrho^U(\mathcal{B}) = \sum_{\mathcal{A} : \mathcal{A}|_U = \mathcal{B}} \varrho(\mathcal{A})$ be the marginal recombination rate. The partitioning process $(\Sigma_t)_{t \ge 0}$ is the Markov chain on partitions of $S$ started at $\Sigma_0 = \{S\}$ in which each block $A$ of the current partition is split independently into the two blocks of $\mathfrak{a}$ at rate $\varrho^A(\mathfrak{a})$. Tracing back the ancestry of the sites of one sampled individual in the ancestral recombination graph converges, as population size $N \to \infty$, to this process: blocks are sets of sites that share an ancestor.

**Theorem.** The solution of the recombination equation with initial value $\omega_0$ is

$$\omega_t = \sum_{\mathcal{A}} a_t(\mathcal{A}) \, R_{\mathcal{A}}(\omega_0) = \mathbb{E}\big[R_{\Sigma_t}(\omega_0) \,\big|\, \Sigma_0 = \{S\}\big], \qquad a_t(\mathcal{A}) = P(\Sigma_t = \mathcal{A} \mid \Sigma_0 = \{S\}) = \big(e^{tQ}\big)_{\{S\}, \mathcal{A}},$$

where $Q$ is the generator of the partitioning process. If moreover every pair of neighbouring sites can be separated, the partitioning process is absorbed in the partition into singletons, and

$$\lim_{t \to \infty} \omega_t = \bigotimes_{i=1}^n \omega_0^{\{i\}}$$

exponentially fast: recombination drives the population to linkage equilibrium. The same representation holds in discrete time with $e^{tQ}$ replaced by $M^t$ for the one-step transition matrix $M$.

## Expansion

The type of an individual at time $t$ is assembled from the types of its ancestors at time $0$: sites in the same block of $\Sigma_t$ come from one ancestor, sites in different blocks from different, independently sampled ancestors, because in an infinite population distinct lineages never coalesce. Since time-$0$ ancestors are drawn from $\omega_0$, the type distribution given $\Sigma_t = \mathcal{A}$ is $R_{\mathcal{A}}(\omega_0)$, and averaging over $\Sigma_t$ gives the formula. This turns a nonlinear ODE on $\boldsymbol{P}(X)$ into a finite linear Markov chain on partitions.

## Sources

- E. Baake and M. Baake, "Ancestral lines under recombination", arXiv:2002.08658 (2020), Section 2 (recombinators), Section 3 (Proposition 3.1, Theorem 3.2, Corollary 3.7), Theorem 5.1 for discrete time, <https://doi.org/10.48550/arXiv.2002.08658>.
