# State-transition-based local network entropy

**Setting.** Let $G$ be a molecular interaction network on $n$ nodes with expression vector $Z(t)$ sampled at discrete times, and let $x_i(t) \in \{0, 1\}$ be the transition variable of node $i$: $x_i(t) = 1$ if $|z_i(t) - z_i(t-1)| > d_i$ for a node-specific threshold $d_i > 0$, else $0$. Fix a node $i$ with first-order neighbors $i_1, \dots, i_m$, and let

$$X_i(t) = \big(x_i(t), x_{i_1}(t), \dots, x_{i_m}(t)\big) \in \{0,1\}^{m+1}$$

be the *local transition state*, which takes one of $2^{m+1}$ values $A_1, \dots, A_{2^{m+1}}$. Assume $X_i(t)$ is a stationary Markov chain with transition matrix $\mathsf P = (p_{u,v})$, $p_{u,v} = \Pr\big(X_i(t+1) = A_u \mid X_i(t) = A_v\big)$, and stationary distribution $\pi$ with $\mathsf P \pi = \pi$.

**Definition.** The *state-transition-based local network entropy* (SNE) of node $i$ is the entropy rate of this chain,

$$H_i = -\sum_{v} \pi_v \sum_{u} p_{u,v} \log p_{u,v} = H\big(X_i(t) \mid X_i(t-1)\big) = \lim_{T \to \infty} \frac{1}{T}\, H\big(X_i(t), X_i(t+1), \dots, X_i(t+T)\big),$$

and the average SNE over a node set $V'$ is $\bar H = |V'|^{-1} \sum_{i \in V'} H_i$.

**Early-warning statement.** Classify nodes relative to the dominant group of a critical transition (see [Dominant-eigenvalue signature of a critical transition](dominant-eigenvalue-signature-of-a-critical-transition.md)) as DNB core, DNB boundary, non-DNB boundary (first-order neighbors of the DNB), and non-DNB core. As the system approaches the transition, the SNE drops drastically at DNB core nodes, decreases at DNB boundary and non-DNB boundary nodes, and stays nearly constant at non-DNB core nodes. Hence a drastic decrease of the average SNE over the nodes whose SNE decreases is an early-warning signal of the critical transition, and those nodes form a network covering the leading (dominant) network.

## Depends on

- [Dominant-eigenvalue signature of a critical transition](dominant-eigenvalue-signature-of-a-critical-transition.md)

## Expansion

For a stationary Markov chain the chain rule of entropy gives $H(X(t), \dots, X(t+T)) = H(X(t)) + \sum_{s=1}^{T} H(X(t+s) \mid X(t+s-1))$, and each conditional term equals $-\sum_v \pi_v \sum_u p_{u,v} \log p_{u,v}$; dividing by $T$ and letting $T \to \infty$ identifies the conditional entropy with the entropy rate. Near the transition the transition variables of a local network containing DNB nodes become strongly correlated across time (the dominant mode is nearly persistent), so the next local state becomes nearly determined by the current one: the rows of $\mathsf P$ concentrate and the entropy rate falls toward $0$. Local networks centered on non-DNB core nodes see no change in their transition statistics, so their SNE is unchanged. Averaging only over nodes with decreasing SNE suppresses noise from the unchanged majority.

## Sources

- R. Liu, M. Li, Z.-P. Liu, J. Wu, L. Chen, K. Aihara, "Identifying critical transitions and their leading biomolecular networks in complex diseases", *Scientific Reports* 2 (2012) 813. Results, "State transitions in biomolecular networks", "SNE and robustness" (SNE, Eq. (3); average SNE, Eq. (5)) and "Identifying critical transitions and their leading networks using SNE" (four-layer node classification). <https://doi.org/10.1038/srep00813>. PMCID: PMC3517980.
