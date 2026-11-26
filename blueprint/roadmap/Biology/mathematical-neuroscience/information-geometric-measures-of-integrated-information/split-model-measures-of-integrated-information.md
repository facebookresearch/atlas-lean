# Split-model measures of integrated information

**Setting.** A system of $n$ units (for example neurons) has states $X = (X_1, \dots, X_n)$ at time $t$ and $Y = (Y_1, \dots, Y_n)$ at time $t+1$, with finite state spaces and joint law $\tilde P$ on $Z = (X, Y)$. An integrated-information measure is the Kullback-Leibler distance from $\tilde P$ to a **split model** $\mathcal M$ in which causal cross-connections $X_j \to Y_i$ ($j \ne i$) are removed,

$$\Phi_{\mathcal M}(\tilde P) = \inf_{Q \in \mathcal M} D_Z(\tilde P \,\|\, Q).$$

Two desiderata: (Property 1) the split model has no causal cross-influences, $Q(Y_j \mid X) = Q(Y_j \mid X_{I \setminus \{i\}})$ for $i \ne j$; (Property 2) it contains every distribution in which the $Y_i$ are coupled only by correlations allowed without cross-connections.

**Stochastic interaction.** With $\mathcal M_{SI} = \{Q : Q(Y \mid X) = \bigotimes_i Q(Y_i \mid X_i)\}$,

$$\Phi_{SI} = \sum_{i=1}^n H(Y_i \mid X_i) - H(Y \mid X).$$

**Integrated information.** With $\mathcal M_{CIS} = \{Q : Q(Y_i \mid X) = Q(Y_i \mid X_i) \text{ for all } i\}$, i.e. $Y_i \perp X_{I\setminus\{i\}} \mid X_i$, $\Phi_{CIS}$ satisfies both properties; every model satisfying Property 1 is contained in $\mathcal M_{CIS}$, and $\mathcal M_{SI} \subseteq \mathcal M_{CIS}$, so $\Phi_{CIS} \le \Phi_{SI}$.

**Causal information integration.** Add a hidden common exterior influence $W$ with $m$ states, independent of $X$, and let

$$\mathcal M_{CII}^m = \Big\{ P : P(z) = \sum_{j=1}^m Q(x)\, Q(w_j) \prod_{i=1}^n Q(y_i \mid x_i, w_j) \Big\}, \qquad \mathcal M_{CII} = \overline{\textstyle\bigcup_m \mathcal M_{CII}^m}.$$

Then $\Phi_{CII} = 0$ iff $\tilde P$ is a limit of marginals of distributions factoring as $Q(x) Q(w) \prod_i Q(y_i \mid x_i, w)$ (Proposition 1). If $W$ were observed, the divergence to the split model would be

$$\Phi_T = \sum_{i=1}^n I(Y_i ; X_{I \setminus \{i\}} \mid X_i, W) \qquad \text{(Proposition 2)},$$

and $\Phi_{CII} \le \Phi_T$ (Proposition 3). Moreover no chain mixed graph obtained by adding more complicated hidden structure to the stochastic-interaction graph yields a model satisfying Property 1 that strictly contains $\mathcal M_{CII}$ (Theorem 2).

## Expansion

For $\mathcal M_{SI}$ the minimizer keeps $\tilde P(x)$ and replaces the transition kernel by the product of its single-unit marginals, so the divergence is the multi-information of the conditional, $\sum_i H(Y_i \mid X_i) - H(Y \mid X)$. The stochastic interaction violates Property 2: a common external input correlates the $Y_i$ even with no cross-connections, and $\Phi_{SI}$ counts this as integration. $\Phi_{CIS}$ fixes this but is defined only by conditional independences without a graphical model. Introducing the latent $W$ restores a graph: the split model is the marginal of a directed model with edges $X_i \to Y_i$ and $W \to Y_i$ only. With $W$ known, the KL projection onto the factorized family decomposes over units into conditional mutual informations, and minimizing over the unknown $W$ can only lower the value, which gives Proposition 3.

## Sources

- C. Langer, N. Ay, "Complexity as Causal Information Integration", Entropy 22(10) (2020) 1107, Definitions 1-5, Propositions 1-3 and Theorem 2, <https://doi.org/10.3390/e22101107>, PMCID PMC7597220.
