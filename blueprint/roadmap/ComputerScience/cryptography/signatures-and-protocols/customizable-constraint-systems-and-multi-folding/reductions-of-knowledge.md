# Reductions of knowledge between relations

For relations $\mathcal{R}_1$ and $\mathcal{R}_2$, a *reduction of knowledge* from $\mathcal{R}_1$ to $\mathcal{R}_2$ is an interactive protocol between a prover holding $(u_1,w_1)$ and a verifier holding $u_1$, after which the verifier outputs $u_2$ and the prover outputs $w_2$, such that (completeness) $(u_1,w_1)\in\mathcal{R}_1$ implies $(u_2,w_2)\in\mathcal{R}_2$, and (knowledge soundness) from any prover whose output satisfies $\mathcal{R}_2$ with probability $\varepsilon$ an expected polynomial-time extractor recovers $w_1$ with $(u_1,w_1)\in\mathcal{R}_1$ with probability $\varepsilon-\mathrm{negl}(\lambda)$. A folding scheme for $\mathcal{R}$ is a reduction of knowledge from $\mathcal{R}^{2}$ to $\mathcal{R}$; an argument of knowledge is a reduction to the trivial relation.

## Depends on

- [Folding scheme for an NP relation](../relaxed-r1cs-folding-schemes/folding-scheme.md)
- [Knowledge soundness](../zero-knowledge-and-arguments/knowledge-soundness.md)

## Sources

- Abhiram Kothapalli, Bryan Parno, "Algebraic Reductions of Knowledge", CRYPTO (2023).
