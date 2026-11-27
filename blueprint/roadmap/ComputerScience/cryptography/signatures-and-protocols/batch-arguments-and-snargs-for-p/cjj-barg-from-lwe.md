# Batch arguments for NP from LWE

Assuming the polynomial hardness of LWE, there is a BARG for NP, in the common random string model, with semi-adaptive somewhere soundness and the following parameters: to prove $k$ instances of a language whose NP relation is decided by a Turing machine in time $T$, with instances of length $n$ and witnesses of length $m$, the reference string and the proof have size $\mathrm{poly}(\log k,\log T,n,m,\lambda)$, the prover runs in time $\mathrm{poly}(k,T,n,m,\lambda)$, and the verifier runs in time $\mathrm{poly}(\log k,\log T,n,m,\lambda)+\mathrm{poly}(k,n,\lambda)$, the second term covering reading the $k$ instances. For index languages the verifier's dependence on $k$ is polylogarithmic. The guarantees are semi-adaptive somewhere soundness and a somewhere argument of knowledge, both at an index $i^{*}$ fixed before the reference string is generated: with a trapdoor reference string for $i^{*}$, computationally indistinguishable from an honest one, no efficient prover can make the verifier accept when the $i^{*}$-th instance is false, even choosing the instances after seeing the reference string, and an extractor recovers a witness for the $i^{*}$-th instance from any accepting proof. Soundness is not adaptive in the index. By contrast, the earlier batch arguments of the same authors from QR together with LWE or sub-exponential DDH have proof size $\tilde{O}((|C|+\sqrt{k|C|})\cdot\lambda)$, sublinear but not polylogarithmic in $k$, and only non-adaptive soundness.

## Proof sketch

Build a BARG for index languages from a PCP with fast online verification: the prover commits to all $k$ PCP proofs with a somewhere extractable commitment, and the queries are made non-interactive by Fiat–Shamir with a hash family that is correlation intractable for the bad-challenge relation, built from LWE. In trapdoor mode at index $i^{*}$ the committed PCP at $i^{*}$ is statistically bound, so an accepting proof for a false instance at $i^{*}$ breaks correlation intractability. A recursive construction reduces the dependence on $k$ to polylogarithmic, and a BARG for NP is obtained from one for index languages.

## Depends on

- [Non-interactive batch arguments for NP](batch-argument.md)
- [Somewhere extractable (somewhere statistically binding) hash functions](somewhere-extractable-hash.md)
- [Learning with errors](../../public-key/hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [Correlation intractability and NIZK for NP from LWE](ci-from-lwe.md)

## Sources

- Arka Rai Choudhuri, Abhishek Jain, Zhengzhong Jin, "SNARGs for P from LWE", FOCS (2021), IACR ePrint 2021/808, Theorem 2, Sections 2.3 and 4 (Section 4.1 and Remark 2 after Lemma 9 for the somewhere argument of knowledge).
- Arka Rai Choudhuri, Abhishek Jain, Zhengzhong Jin, "Non-Interactive Batch Arguments for NP from Standard Assumptions", CRYPTO (2021), IACR ePrint 2021/807 (the earlier sublinear, non-adaptively sound construction).
