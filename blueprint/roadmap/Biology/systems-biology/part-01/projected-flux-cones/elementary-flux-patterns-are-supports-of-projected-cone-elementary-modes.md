# Elementary flux patterns are supports of projected cone elementary modes

**Setting.** As for [projected cone elementary modes](projected-cone-elementary-modes-are-projected-elementary-modes.md), consider a metabolic network with irreversible reactions only, its flux cone $C$, and the projection $P_X(C)$ onto a subnetwork of interesting reactions. A *flux pattern* is a set of subnetwork reactions that equals the support (restricted to the subnetwork) of some steady-state flux vector of the whole network; an *elementary flux pattern* (EFP) is a flux pattern that is not the union of two or more different flux patterns.

**Theorem.** If $\mathcal{E}$ is the set of EFPs and $\mathcal{J}$ the set of ProCEMs, then

$$\mathcal{E} \subseteq \{\operatorname{supp}(u) : u \in \mathcal{J}\}.$$

So every EFP is recovered from the ProCEMs, while ProCEMs additionally carry the flux ratios inside a mode, and some ProCEM supports are not EFPs. Given the ProCEMs, the EFPs are obtained by discarding every ProCEM support that is a union of other ProCEM supports.

## Depends on

- [Projected cone elementary modes are projected elementary modes](projected-cone-elementary-modes-are-projected-elementary-modes.md)

## Expansion

Suppose an EFP $F$ is not the support of any ProCEM. Since $F$ is an EFP it is the support of some PEM $p \in P_X(C)$, which therefore is not a ProCEM, so $p = \sum_{k=1}^r c_k u_k$ with $r \ge 2$ distinct ProCEMs $u_k$ and $c_k > 0$. All vectors are nonnegative, hence $\operatorname{supp}(p) = \bigcup_k \operatorname{supp}(u_k)$ with each $\operatorname{supp}(u_k) \ne \operatorname{supp}(p)$. Each $\operatorname{supp}(u_k)$ is a flux pattern, so $F$ is a union of other flux patterns, contradicting elementarity.

## Sources

- S.-A. Marashi, L. David, A. Bockmayr, "Analysis of metabolic subnetworks by flux cone projection", Algorithms for Molecular Biology 7 (2012) 17, Theorem 2 and Algorithm 1 (Table 2), <https://doi.org/10.1186/1748-7188-7-17>, PMCID PMC3408373.
