# Non-interactive batch arguments for NP

A *non-interactive batch argument (BARG)* for circuit satisfiability consists of $\mathsf{Gen}(1^\lambda,1^{k},1^{|C|})\to\mathsf{crs}$, $\mathsf{P}(\mathsf{crs},C,x_1,\dots,x_k,w_1,\dots,w_k)\to\pi$ and $\mathsf{V}(\mathsf{crs},C,x_1,\dots,x_k,\pi)$. *Completeness:* if $C(x_i,w_i)=1$ for all $i$ then $\mathsf{V}$ accepts. *Soundness:* for every efficient adversary producing $C,x_1,\dots,x_k,\pi$ with some $x_i$ having no witness, $\mathsf{V}$ rejects except with negligible probability. *Succinctness:* $|\pi|\le\mathrm{poly}(\lambda,|C|,\log k)$, much smaller than the $k$ witnesses. A BARG is *somewhere extractable* if $\mathsf{crs}$ can be generated in a trapdoor mode binding to an index $i^{*}$ hidden from the adversary, from which a valid $w_{i^{*}}$ is extracted from any accepting proof.

## Depends on

- [Interactive arguments](../zero-knowledge-and-arguments/interactive-arguments.md)

## Sources

- Arka Rai Choudhuri, Abhishek Jain, Zhengzhong Jin, "Non-Interactive Batch Arguments for NP from Standard Assumptions", CRYPTO (2021), IACR ePrint 2021/807.
- Yael Tauman Kalai, Omer Paneth, Lisa Yang, "How to Delegate Computations Publicly", STOC (2019), IACR ePrint 2018/776.
