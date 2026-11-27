# Stationary distribution of a rank-one perturbed gene network chain

**Network chain.** In a Boolean network with perturbation (BNp) on $n$ genes with network function $f : \{0,1\}^n \to \{0,1\}^n$, each gene is flipped independently with probability $p$ at each step; otherwise the state is updated by $f$. The transition probability from $y$ to $x$ is

$$P_y(x) = (1-p)^n\,\mathbf 1[f(y) = x] + p^{\eta(x,y)}(1-p)^{n-\eta(x,y)}\,\mathbf 1[x \ne y],$$

where $\eta$ is Hamming distance; an instantaneously random PBN with network functions $f_1,\dots,f_m$ chosen with probabilities $c_1,\dots,c_m$ replaces the indicator by $\sum_l c_l\mathbf 1[f_l(y) = x]$. For $p > 0$ the chain is irreducible and aperiodic with stationary distribution $\pi$, $\pi^{\mathsf T}P = \pi^{\mathsf T}$, and fundamental matrix $Z = (I - P + e\pi^{\mathsf T})^{-1}$.

**Theorem (rank-one perturbation).** Let $\tilde P = P + ab^{\mathsf T}$ be a stochastic irreducible perturbation, so $b^{\mathsf T}e = 0$. Then

$$\tilde\pi^{\mathsf T} = \pi^{\mathsf T} + \frac{\pi^{\mathsf T}a}{1 - b^{\mathsf T}Za}\;b^{\mathsf T}Z,$$

and the perturbed fundamental matrix is likewise an explicit rank-one update of $Z$.

**Corollary (gene flipping at one state).** If control flips gene $g$ whenever the network is in state $x$, row $p_x$ of $P$ is replaced by the row $p_{\tilde x}$ of the flipped state $\tilde x$, i.e. $a = e_x$, $b = p_{\tilde x} - p_x$, and

$$\tilde\pi^{\mathsf T}(x) = \pi^{\mathsf T} + \frac{\pi_x}{1 - (p_{\tilde x} - p_x)^{\mathsf T}z_x}\,(p_{\tilde x} - p_x)^{\mathsf T}Z,$$

with $z_x$ the column of $Z$ indexed by $x$.

## Proof depends on

- [Existence of a stationary distribution](../../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/exists-stationary.md)
- [Uniqueness of the stationary distribution of a primitive chain](../../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/stationary-unique.md)

## Expansion

The BNp formula separates the event that no gene is perturbed (probability $(1-p)^n$, deterministic update) from the event that exactly the genes in which $x$ and $y$ differ are perturbed. For the perturbation theorem, write $\tilde\pi^{\mathsf T}(I - \tilde P) = 0$ as $\tilde\pi^{\mathsf T}(I - P) = (\tilde\pi^{\mathsf T}a)\,b^{\mathsf T}$; multiplying by $Z$ and using $(I-P)Z = I - e\pi^{\mathsf T}$, $b^{\mathsf T}e = 0$ and $\tilde\pi^{\mathsf T}e = 1$ gives $\tilde\pi^{\mathsf T} = \pi^{\mathsf T} + (\tilde\pi^{\mathsf T}a)\,b^{\mathsf T}Z$; solving for the scalar $\tilde\pi^{\mathsf T}a$ yields the formula. The shift of mass caused by any single-state intervention therefore costs one vector–matrix product once $\pi$ and $Z$ are known.

## Sources

- X. Qian, I. Ivanov, N. Ghaffari, E. R. Dougherty, "Intervention in gene regulatory networks via greedy control policies based on long-run behavior", BMC Systems Biology 3 (2009) 61, Theorems 1–3 and the gene-flipping specialization, <https://doi.org/10.1186/1752-0509-3-61>, PMCID PMC2728102.
