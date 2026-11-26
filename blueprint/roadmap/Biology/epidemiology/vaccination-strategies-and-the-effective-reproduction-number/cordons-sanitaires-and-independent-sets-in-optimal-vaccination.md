# Cordons sanitaires and independent sets in optimal vaccination

**Setting.** A population is described by a probability space $(\Omega,\mu)$ of types and a next-generation kernel $\mathsf k\ge0$ (in a metapopulation model, $\Omega=\{1,\dots,N\}$ with subpopulation sizes $\mu_i$ and $\mathsf k$ the next-generation matrix rescaled by $\mu$). A vaccination strategy $\eta:\Omega\to[0,1]$ is the non-vaccinated fraction; its loss is the effective reproduction number $R_e(\eta)$ (spectral radius of the effective next-generation operator $\mathsf k\eta$) and its cost is a continuous decreasing function $C(\eta)$, for instance the uniform cost $C(\eta)=\int(1-\eta)\,d\mu$. A strategy is *Pareto optimal* if no strategy is at least as good in both cost and loss and strictly better in one, and *anti-Pareto optimal* if it is worst in the same sense. A *cordon sanitaire* (disconnecting strategy) is one for which the effective infection operator among non-vaccinated individuals is reducible: the non-vaccinated population splits into groups $A,B$ with no infection from $B$ to $A$.

**Lemma (reducible splitting).** If $A\cap B=\emptyset$ and $\mathsf k(B,A)=0$, then

$$R_e(\mathbf 1_A+\mathbf 1_B)=\max\big(R_e(\mathbf 1_A),R_e(\mathbf 1_B)\big).$$

More generally, for the Frobenius decomposition of $\Omega$ into irreducible components $\Omega_i$, $R_e(\eta)=\max_i R_e(\eta\mathbf 1_{\Omega_i})$.

**Proposition (cordons are never worst).** If $R_0>0$, no disconnecting strategy is anti-Pareto optimal. A cordon sanitaire need not be Pareto optimal.

**Proposition (cost of eradication via independent sets).** Call $A\subset\Omega$ independent if $\mathsf k=0$ on $A\times A$ almost everywhere, and let $\alpha(\mathsf k)$ be the supremum of $\mu(A)$ over independent sets; a maximal independent set attaining it exists. If the support $\{\mathsf k>0\}$ is symmetric and the cost is uniform, then for any maximal independent set $A_\star$ the strategy $\mathbf 1_{A_\star}$ (vaccinate everyone outside $A_\star$) is Pareto optimal and the minimal cost achieving $R_e=0$ is

$$C(\mathbf 1_{A_\star})=1-\alpha(\mathsf k).$$

## Expansion

If the non-vaccinated set is independent, no infection is possible, so $R_e=0$; conversely, with symmetric support, a strategy with $R_e(\eta)=0$ must leave a non-vaccinated set on which the kernel vanishes, so the cheapest eradication vaccinates the complement of a largest independent set (for the cycle graph on $N$ vertices this costs $1-\lfloor N/2\rfloor/N$). For the cordon result, splitting along a reducible decomposition replaces $R_e$ of the whole by the maximum over pieces, and one can always find a strategy of the same cost that is strictly worse, e.g. by moving vaccine away from the part realizing the maximum. The block-triangular structure also gives the full Pareto and anti-Pareto frontiers of a reducible kernel as maxima over irreducible components.

## Depends on

- [Convexity and concavity of the effective reproduction number in the vaccination profile](convexity-and-concavity-of-the-effective-reproduction-number-in-the-vaccination-profile.md)

## Sources

- Jean-François Delmas, Dylan Dronnier, Pierre-André Zitt, "Effective reproduction number: Convexity, invariance and cordons sanitaires", arXiv:2110.12693: Proposition 6.6 and Lemma 6.7 (cordons sanitaires), Definition 6.9 and Propositions 6.10–6.11 (independent sets and the cost of eradication), Lemma 7.2 and Corollary 7.4 (reducible kernels), Example 1.2 (cycle graph). <https://doi.org/10.48550/arXiv.2110.12693>
