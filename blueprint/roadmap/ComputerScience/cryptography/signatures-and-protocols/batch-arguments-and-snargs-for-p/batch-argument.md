# Non-interactive batch arguments for NP

A *non-interactive batch argument (BARG)* for circuit satisfiability, $\mathrm{SAT}=\{(C,x):\exists w,\ C(x,w)=1\}$, consists of algorithms $\mathsf{Gen}(1^\lambda,1^{k},1^{|C|})\to\mathsf{crs}$, a trapdoor generator $\mathsf{TGen}(1^\lambda,1^{k},1^{|C|},i^{*})\to\mathsf{crs}^{*}$, a prover $\mathsf{P}(\mathsf{crs},C,x_1,\dots,x_k,w_1,\dots,w_k)\to\pi$ and a verifier $\mathsf{V}(\mathsf{crs},C,x_1,\dots,x_k,\pi)$. *Completeness:* if $C(x_i,w_i)=1$ for all $i$, then $\mathsf{V}$ accepts with probability $1$. *CRS indistinguishability:* for every index $i^{*}$ chosen by an efficient adversary, $\mathsf{Gen}$ and $\mathsf{TGen}(\cdot,i^{*})$ give computationally indistinguishable reference strings. *Semi-adaptive somewhere soundness:* for every efficient adversary that first declares $i^{*}\in[k]$, then receives $\mathsf{crs}^{*}\leftarrow\mathsf{TGen}(\cdot,i^{*})$ and outputs $C,x_1,\dots,x_k,\pi$, the probability that $(C,x_{i^{*}})\notin\mathrm{SAT}$ and $\mathsf{V}$ accepts is negligible; the circuit and the instances may depend on the reference string, but the index may not. *Succinctness* asks the proof to be shorter than the $k$ witnesses: in general sublinear in $k$, for example $\mathrm{poly}(\lambda,|C|)\cdot k^{1-\epsilon}$; the stronger target, achieved in the strongest constructions, is proof and reference string size $\mathrm{poly}(\lambda,\log k,|C|)$. A BARG for an *index language* is one whose instances are the indices $1,\dots,k$ themselves, with $C$ hard-wiring the common data, so that the verifier need not read $k$ separate instances.

## Depends on

- [Interactive arguments](../zero-knowledge-and-arguments/interactive-arguments.md)

## Sources

- Arka Rai Choudhuri, Abhishek Jain, Zhengzhong Jin, "SNARGs for P from LWE", FOCS (2021), IACR ePrint 2021/808, Section 2.2 and Section 4.1 (definition with semi-adaptive somewhere soundness and polylogarithmic succinctness).
- Arka Rai Choudhuri, Abhishek Jain, Zhengzhong Jin, "Non-Interactive Batch Arguments for NP from Standard Assumptions", CRYPTO (2021), IACR ePrint 2021/807 (sublinear batch arguments with non-adaptive soundness).
- Yael Tauman Kalai, Omer Paneth, Lisa Yang, "How to Delegate Computations Publicly", STOC (2019), IACR ePrint 2019/603 (publicly verifiable non-interactive delegation for polynomial-time computations from a decisional assumption on bilinear groups, the delegation problem that the batch-argument approach above addresses from standard assumptions).
