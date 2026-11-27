# Delegation for deterministic computation from BARGs and somewhere extractable commitments

Let $M$ be a deterministic machine running for $T$ steps with states $\mathrm{st}_1,\dots,\mathrm{st}_T$. The prover commits to the sequence of states with a somewhere extractable commitment with succinct local openings and proves, with a BARG for the index language, the $T-1$ statements "for index $i$, the committed $\mathrm{st}_i$ and $\mathrm{st}_{i+1}$ (opened locally) satisfy $\mathrm{Step}(\mathrm{st}_i)=\mathrm{st}_{i+1}$, $\mathrm{st}_1$ encodes the input $x$ when $i=1$, and $\mathrm{st}_T$ is accepting when $i=T-1$", where the circuit hard-wires the commitment and $x$. Three distinct guarantees are combined: the BARG is semi-adaptively somewhere sound; the commitment is somewhere extractable, so that a key generated in trapdoor mode for a hidden set $S$ of positions lets one extract the unique values at $S$ from any commitment, even one produced by an unbounded prover, with an extractor that is computationally no-signaling across sets of bounded size; and the resulting delegation scheme is adaptively sound, against a prover that chooses the input after seeing the keys. With polylogarithmic BARGs and commitments, and the memory hashed into a tree so that each local statement has size $\mathrm{poly}(\lambda,\log T)$, the reference string, the proof and the verifier's work beyond reading the input are $\mathrm{poly}(\lambda,\log T)$, and the prover runs in time $\mathrm{poly}(\lambda,T)$.

## Proof sketch

For each $i$ consider the experiment with the BARG trapdoor at index $i$ and the commitment trapdoor at the positions of $\mathrm{st}_i$ and $\mathrm{st}_{i+1}$. Statistical binding at those positions makes the $i$-th index statement false whenever the extracted states violate $\mathrm{Step}$, so semi-adaptive somewhere soundness shows the extracted $\mathrm{st}_{i+1}$ follows from the extracted $\mathrm{st}_i$ in an accepting proof. The no-signaling property makes the extracted $\mathrm{st}_{i+1}$ indistinguishable between the experiments for $i$ and $i+1$, so by induction on $i$ the extracted states are the correct states of $M$ on the chosen input. At $i=T-1$ an accepting proof for a rejecting computation gives a contradiction.

## Depends on

- [Non-interactive batch arguments for NP](batch-argument.md)
- [Somewhere extractable (somewhere statistically binding) hash functions](somewhere-extractable-hash.md)

## Sources

- Arka Rai Choudhuri, Abhishek Jain, Zhengzhong Jin, "SNARGs for P from LWE", FOCS (2021), IACR ePrint 2021/808, Theorem 1, Section 2.2 and Section 5.
- Yael Tauman Kalai, Omer Paneth, Lisa Yang, "How to Delegate Computations Publicly", STOC (2019), IACR ePrint 2019/603 (the earlier publicly verifiable delegation scheme, whose quasi-arguments also address the local-to-global soundness problem).
- Yael Tauman Kalai, Vinod Vaikuntanathan, Rachel Yun Zhang, "Somewhere Statistical Soundness, Post-Quantum Security, and SNARGs", TCC (2021) (an independent derivation of SNARGs for deterministic computation from batch arguments).
