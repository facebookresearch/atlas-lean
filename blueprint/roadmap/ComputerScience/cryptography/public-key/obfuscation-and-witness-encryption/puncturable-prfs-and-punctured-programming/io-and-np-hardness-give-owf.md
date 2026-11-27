# Indistinguishability obfuscation plus worst-case hardness of NP yields one-way functions

If there exists an indistinguishability obfuscator for polynomial-size circuits (even an imperfect one, which preserves functionality only with overwhelming probability over its randomness) and $\mathsf{NP}\not\subseteq\mathsf{ioBPP}$, then one-way functions exist. Thus iO by itself is not a "cryptographic" assumption only in the trivial world where NP is easy infinitely often.

## Proof sketch

Consider the function mapping randomness to an obfuscation of the constant-zero circuit. If it were invertible, then given an obfuscation of an arbitrary circuit $C$ one could decide whether $C$ is unsatisfiable, since inverting succeeds on $\mathcal{O}(C)$ essentially only when $C$ is equivalent to the zero circuit, by iO security; this decides circuit satisfiability in $\mathsf{ioBPP}$.

## Depends on

- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)
- [One-way functions exist](../../../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/impagliazzo-s-five-worlds/owfexists.md)

## Proof depends on

- [One-way functions imply P ≠ NP](../../../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/owf-implies-p-ne-np.md)

## Sources

- Ilan Komargodski, Tal Moran, Moni Naor, Rafael Pass, Alon Rosen, Eylon Yogev, "One-Way Functions and (Im)perfect Obfuscation", FOCS (2014), IACR ePrint 2014/347, Theorem 4.1.
