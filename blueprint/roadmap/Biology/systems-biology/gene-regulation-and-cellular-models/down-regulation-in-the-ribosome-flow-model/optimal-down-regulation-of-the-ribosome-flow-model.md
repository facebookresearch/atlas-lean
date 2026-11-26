# Optimal down-regulation of the ribosome flow model

**Model.** The ribosome flow model (RFM) with $n$ sites has normalised ribosome densities $x_i(t) \in [0,1]$ and positive transition rates $\lambda_0$ (initiation), $\lambda_1, \dots, \lambda_{n-1}$ (elongation) and $\lambda_n$ (exit):

$$\dot x_i = \lambda_{i-1} x_{i-1}(1 - x_i) - \lambda_i x_i (1 - x_{i+1}), \qquad i = 1,\dots,n,$$

with the conventions $x_0 \equiv 1$, $x_{n+1} \equiv 0$. The unit cube is invariant, there is a unique globally asymptotically stable steady state $e(\lambda) \in (0,1)^n$, and the production rate $R(t) = \lambda_n x_n(t)$ converges to $R(\lambda) = \lambda_n e_n(\lambda)$.

**Spectral facts used.** $R(\lambda) = \zeta^{-2}$, where $\zeta$ is the largest eigenvalue of the $(n+2) \times (n+2)$ symmetric tridiagonal matrix with zero diagonal and off-diagonal entries $\lambda_0^{-1/2}, \dots, \lambda_n^{-1/2}$. Consequently $R$ is positively homogeneous of degree one, strictly increasing in every rate, and strictly concave on $\mathbb R^{n+1}_{>0}$; the sensitivities $s_i = \partial R / \partial \lambda_i$ are computable from the Perron eigenvector.

**Problem (budgeted down-regulation).** Given rates $\lambda$ and a total reduction budget $b > 0$ small enough that all reduced rates stay positive, minimise $R(\eta)$ over the simplex $\Omega = \{\lambda - v : v \in \mathbb R^{n+1}_{\ge 0},\ \sum_i v_i = b\}$, whose vertices are $\lambda - b\, e_i$, $i = 0, \dots, n$.

1. **Extremality.** For any compact convex feasible set of rates, every minimiser of $R$ is an extreme point; in particular every optimum of the budgeted problem reduces a single rate by the whole budget $b$.
2. **Sensitivity rule.** If $s_i(\lambda) < s_j(\lambda)$ for some $j$, then every optimum leaves $\lambda_i$ unchanged. Hence if $\lambda_k$ is a *bottleneck rate* (strictly maximal sensitivity), the unique optimum is $\lambda - b\, e_k$. The bottleneck need not be the slowest rate.
3. **Homogeneous chain.** If all rates are equal, the unique optimum for even $n$ reduces the middle rate $\lambda_{n/2}$; for odd $n$ the two optima reduce $\lambda_{(n-1)/2}$ or $\lambda_{(n+1)/2}$ (edge effect: the output is least sensitive to rates near the ends).
4. **Equal occupancies.** If the rates make all steady-state densities equal to a common value $e_c$, the unique optimum reduces the initiation rate $\lambda_0$ when $e_c < 1/2$ and the exit rate $\lambda_n$ when $e_c > 1/2$; for $e_c = 1/2$ both are optimal.

## Expansion

A strictly concave function attains its minimum over a compact convex set only at extreme points (otherwise write the minimiser as a proper convex combination and use concavity), giving item 1. On the simplex $\Omega$ the candidates are the $n+1$ vertices; comparing $R(\lambda - b e_i)$ with $R(\lambda - b e_j)$ via concavity and the gradient at $\lambda$ shows that a vertex reducing a less sensitive rate can never be optimal, which is item 2. Reducing a rate increases its own sensitivity (concavity), so a rate that is reduced enough eventually becomes the bottleneck. Items 3 and 4 follow by computing the sensitivity profile explicitly: for equal rates it peaks at the centre of the chain, and for equal occupancies it is maximised at the left end when the lattice is sparse and at the right end when it is crowded, matching the particle–hole symmetry of the RFM (replacing $x_i$ by $1 - x_{n+1-i}$ reverses the order of the rates). The same structure was observed in stochastic exclusion simulations. In biological terms, the fewest-mutation way to slow translation of a gene targets its most sensitive codon, which is not necessarily its slowest one.

## Sources

- Y. Zarai, M. Margaliot, T. Tuller, "Optimal down regulation of mRNA translation", *Scientific Reports* (2017), sections "The Ribosome Flow Model", "Steady-State Spectral Representation" (Theorem 1, citing earlier work) and "Main Results" (Problems 1–2, Propositions 1–4, Definition 1, Corollary 1, Remark 1, Examples 3–4), <https://doi.org/10.1038/srep41243> (PMC5264618).
