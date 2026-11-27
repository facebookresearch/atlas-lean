# SNARGs for all polynomial-time computations from LWE

Assuming the polynomial hardness of LWE, for every polynomial $T=T(\lambda)$ there is a publicly verifiable non-interactive delegation scheme, in the common random string model, for every Turing machine $M$ running in time $T$: for the language $\{(x,T):M\text{ accepts }x\text{ within }T\text{ steps}\}$, the reference string size, the proof size and the verifier's running time beyond reading the input are $\mathrm{poly}(\lambda,\log T)$, the verifier reads the input in time $|x|\cdot\mathrm{poly}(\lambda)$, and the prover runs in time $\mathrm{poly}(\lambda,T)$. Soundness is adaptive: no efficient prover that chooses $x$ after seeing the keys can make the verifier accept $x$ outside the language, except with negligible probability. The result extends with the same parameters to RAM computations.

## Proof sketch

Instantiate the delegation-from-BARG template with the LWE-based BARG for index languages, which is semi-adaptively somewhere sound, and with LWE-based somewhere extractable commitments made no-signaling, hashing the memory into a tree so that each local step statement has size $\mathrm{poly}(\lambda,\log T)$. Adaptive soundness of the delegation scheme follows from the step-by-step hybrid argument, since the index each hybrid fixes in advance does not depend on the prover's choice of input.

## Depends on

- [Learning with errors](../../public-key/hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [Delegation for deterministic computation from BARGs and somewhere extractable commitments](snarg-from-barg-and-hash.md)
- [Batch arguments for NP from LWE](cjj-barg-from-lwe.md)

## Sources

- Arka Rai Choudhuri, Abhishek Jain, Zhengzhong Jin, "SNARGs for P from LWE", FOCS (2021), IACR ePrint 2021/808, Theorem 1, Definition 8 and Theorem 11.
