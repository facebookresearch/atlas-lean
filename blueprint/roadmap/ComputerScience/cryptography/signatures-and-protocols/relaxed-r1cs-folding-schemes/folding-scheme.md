# Folding scheme for an NP relation

Let $\mathcal{R}$ be a relation over public parameters $pp$, structures $s$, instances $u$ and witnesses $w$. A *folding scheme* for $\mathcal{R}$ is a tuple $(\mathsf{G},\mathsf{K},\mathsf{P},\mathsf{V})$ where $\mathsf{K}(pp,s)$ outputs prover and verifier keys, and an interactive protocol between $\mathsf{P}(\mathsf{pk},(u_1,w_1),(u_2,w_2))$ and $\mathsf{V}(\mathsf{vk},u_1,u_2)$ ends with $\mathsf{V}$ outputting a folded instance $u$ and $\mathsf{P}$ outputting a folded witness $w$. *Perfect completeness:* if $(pp,s,u_i,w_i)\in\mathcal{R}$ for $i=1,2$ then $(pp,s,u,w)\in\mathcal{R}$. *Knowledge soundness:* for every expected polynomial-time adversary choosing $s,u_1,u_2$ and a prover $\mathsf{P}^*$ that outputs a valid folded witness with probability $\varepsilon$, there is an expected polynomial-time extractor outputting witnesses $w_1,w_2$ for $u_1,u_2$ with probability at least $\varepsilon-\mathrm{negl}(\lambda)$. A folding scheme is thus a reduction of knowledge from $\mathcal{R}\times\mathcal{R}$ to $\mathcal{R}$, weaker than a proof system because the verifier does not decide membership.

## Depends on

- [Knowledge soundness](../zero-knowledge-and-arguments/knowledge-soundness.md)
- [Interactive arguments](../zero-knowledge-and-arguments/interactive-arguments.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, Ioanna Tzialla, "Nova: Recursive Zero-Knowledge Arguments from Folding Schemes", CRYPTO (2022), IACR ePrint 2021/370.
