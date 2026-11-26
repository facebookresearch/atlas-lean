# SNARGs for all polynomial-time computations from LWE

Assuming the polynomial hardness of LWE, for every polynomial $T$ there is a publicly verifiable succinct non-interactive argument for all deterministic computations of $T$ steps (the language $\{(M,x,y,T):M(x)=y\text{ within }T\text{ steps}\}$) in which the common reference string size, the proof size and the verification time are $\mathrm{poly}(\lambda,\log T)$ (plus the time to read $M,x,y$). Soundness is non-adaptive with respect to the statement.

## Proof sketch

Instantiate the delegation-from-BARG template with the LWE-based somewhere extractable BARG and SSB hashes, compressing configurations by Merkle-hashing the memory so that each local step statement has size $\mathrm{poly}(\lambda,\log T)$. Soundness follows by the step-by-step hybrid argument.

## Depends on

- [Learning with errors](../../public-key/hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [Delegation for deterministic computation from BARGs and somewhere extractable commitments](snarg-from-barg-and-hash.md)
- [Batch arguments for NP from LWE](cjj-barg-from-lwe.md)

## Sources

- Arka Rai Choudhuri, Abhishek Jain, Zhengzhong Jin, "SNARGs for P from LWE", FOCS (2021), IACR ePrint 2021/808.
