# Delegation for deterministic computation from BARGs and somewhere extractable commitments

Let $M$ be a deterministic machine running for $T$ steps with configurations of size $S$. The prover commits to the sequence of configurations $c_0,\dots,c_T$ with a somewhere extractable hash and proves with a BARG the $T$ local statements "the committed $c_{t}$ and $c_{t+1}$ (opened locally) satisfy the transition function of $M$", together with openings of $c_0$ and $c_T$. If the BARG and hash are somewhere extractable and the hash supports extraction at two positions simultaneously, then soundness holds: any accepting proof for a false output yields, by a hybrid over $t$ that moves the extraction positions, a step $t$ where the extracted $c_t$ is correct but $c_{t+1}$ is not, contradicting somewhere extractability. The proof size is $\mathrm{poly}(\lambda,\log T,S)$, and with further compression of configurations (Merkle-hashed memory) it becomes $\mathrm{poly}(\lambda,\log T)$.

## Proof sketch

By induction on $t$, using indistinguishability of extraction positions, the extracted configuration at position $t$ equals the true $t$-th configuration with overwhelming probability: if true at $t$, local soundness at the pair $(t,t+1)$ forces correctness at $t+1$. At $t=T$ this contradicts the claimed false output.

## Depends on

- [Non-interactive batch arguments for NP](batch-argument.md)
- [Somewhere extractable (somewhere statistically binding) hash functions](somewhere-extractable-hash.md)
- [Somewhere statistical soundness of arguments](somewhere-statistical-soundness.md)

## Proof depends on

- [Somewhere extractable (somewhere statistically binding) hash functions](somewhere-extractable-hash.md)
- [Non-interactive batch arguments for NP](batch-argument.md)

## Sources

- Arka Rai Choudhuri, Abhishek Jain, Zhengzhong Jin, "SNARGs for P from LWE", FOCS (2021), IACR ePrint 2021/808.
- Yael Tauman Kalai, Omer Paneth, Lisa Yang, "How to Delegate Computations Publicly", STOC (2019), IACR ePrint 2018/776.
- Yael Tauman Kalai, Vinod Vaikuntanathan, Rachel Yun Zhang, "Somewhere Statistical Soundness, Post-Quantum Security, and SNARGs", TCC (2021).
