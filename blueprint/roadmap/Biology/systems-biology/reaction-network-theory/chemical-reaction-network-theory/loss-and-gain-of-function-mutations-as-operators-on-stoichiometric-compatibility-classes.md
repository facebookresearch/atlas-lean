# Loss- and gain-of-function mutations as operators on stoichiometric compatibility classes

Let a chemical reaction network with $n$ species and $r$ reactions evolve by $\dot x = S v(x, k)$, $x \in \mathbb R^n_{\ge 0}$, with stoichiometric matrix $S \in \mathbb R^{n \times r}$. A vector $\gamma \in \ker(S^{\top}) \cap \mathbb N^n \setminus \{0\}$ is a semi-positive conservation vector, since $\tfrac{d}{dt}\gamma^{\top}x = \gamma^{\top}Sv = 0$. Let $\gamma_1, \dots, \gamma_p$ be generators forming a basis of $\ker(S^{\top})$ ($p = n - \operatorname{rank} S$) and $N$ the matrix with rows $\gamma_k^{\top}$, so $Nx(t) = Nx_0 = c$. The **stoichiometric compatibility class** of $x$ is $SC(x) = (x + \operatorname{span} S) \cap \mathbb R^n_{\ge 0} = \{y \ge 0 : Ny = Nx\}$. The network is **weakly elemented** if, after reordering, $N = [I_p, N_2]$, so $x = (x_1, x_2)$ with elemental species $x_1 = c - N_2 x_2$ (free proteins, each in exactly one conservation law) and compounds $x_2$. It satisfies the **global stability condition** if each compatibility class contains a unique globally asymptotically stable state.

**Loss of function.** The null loss-of-function mutation of elemental species $A_j$ is the projection $P_{L_j}(x) = (\tilde x_1, \tilde x_2)$ with $\tilde x_{2,i} = 0$ if $\gamma_{ji} \ne 0$ and $\tilde x_{2,i} = x_{2,i}$ otherwise, and $\tilde x_1 = \tilde c - N_2\tilde x_2$, where $\tilde c$ equals $c = Nx$ with its $j$-th entry set to $0$.

**Gain of function.** For a set $H$ of deactivation reactions, the gain-of-function mutation replaces $S$ by $G_H(S)$, obtained by zeroing the columns indexed by $H$ (equivalently, setting those rate constants to $0$).

**Theorem.**
1. If $SC(x) = SC(y)$, then $N P_{L_j}(x) = N P_{L_j}(y) = \tilde c$, so $SC(P_{L_j}(x)) = SC(P_{L_j}(y))$. Under the global stability condition, trajectories from $P_{L_j}(x)$ and $P_{L_j}(y)$ converge to the same mutated steady state; in particular the mutated steady state is the same whether the mutation is applied to the initial state $x_0$ or to the healthy steady state $x_e$.
2. If $\operatorname{rank} G_H(S) = \operatorname{rank} S$, then $\ker G_H(S)^{\top} = \ker S^{\top}$, so the mutated and healthy networks have the same compatibility classes. If both networks satisfy the global stability condition, then initial states in one class of the healthy network converge, under the mutated dynamics $\dot x = G_H(S) v(x,k)$, to one common mutated steady state.

## Depends on

- [Stoichiometric subspace](../../../../Dynamics/smooth-dynamics/stoichiometric-subspace.md)

## Expansion

Part 1 is a direct computation: $N P_{L_j}(x) = \tilde x_1 + N_2\tilde x_2 = \tilde c$, which depends on $x$ only through $c = Nx$; removing the elemental species $A_j$ and all compounds containing it sets the total of its conservation law to zero while leaving the other totals unchanged. Part 2 uses $\ker S^{\top} \subseteq \ker G_H(S)^{\top}$ (a vector orthogonal to all columns is orthogonal to the remaining ones), and equal rank gives equal dimension, hence equality. The global stability condition then reduces the comparison of healthy and mutated long-term behaviour to the comparison of two steady states determined by the conserved totals, which is how such networks are used to simulate the effect of oncogenic mutations (for example in G1–S cell-cycle signalling) without re-simulating from the original initial condition. When removing reactions drops the rank, new conservation laws appear and the mutated network has finer compatibility classes, so the long-term state can depend on more of the initial condition.

## Sources

- S. Sommariva, G. Caviglia, M. Piana, "Gain and loss of function mutations in biological chemical reaction networks: a mathematical model with application to colorectal cancer cells", Journal of Mathematical Biology 82 (2021) 55, Definitions 1–7, Propositions 1–2, Theorems 1–2, Remarks 5–6 and Corollary 1, <https://doi.org/10.1007/s00285-021-01607-0>, PMCID PMC8096774.
