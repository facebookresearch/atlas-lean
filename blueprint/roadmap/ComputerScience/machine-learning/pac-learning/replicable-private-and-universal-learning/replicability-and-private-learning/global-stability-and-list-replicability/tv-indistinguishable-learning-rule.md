# Total-variation indistinguishable learning rules

A learning rule $A$, which maps a sample $S$ to a probability distribution $A(S)$ over hypotheses (its posterior), is **$n$-sample $\rho$-TV indistinguishable** if for every distribution $D$ over examples

$$
\mathbb{E}_{S, S' \sim D^n}\big[d_{\mathrm{TV}}(A(S), A(S'))\big] \le \rho,
$$

where $S$ and $S'$ are independent and $d_{\mathrm{TV}}$ is the total variation distance. No shared randomness is involved; the two output distributions are compared directly.

## Depends on

- [Total variation distance between finite measures](../../../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)
- [Global stability and list replicability of learning rules](global-stability-and-list-replicability.md)

## Sources

- A. Kalavasis, A. Karbasi, S. Moran, G. Velegkas, "Statistical Indistinguishability of Learning Algorithms", ICML (2023), arXiv:2305.14311, Definition 4.
