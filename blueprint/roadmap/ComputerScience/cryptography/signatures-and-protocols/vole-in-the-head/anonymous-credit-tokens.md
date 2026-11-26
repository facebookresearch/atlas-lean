# Anonymous credit tokens

An *anonymous credit token* (ACT) scheme lets an issuer certify a hidden state $(\mathrm{nf}, \mathrm{ctx}, t, x)$ consisting of a nullifier, a context, committed credit $t$ and an issuer-granted refund $x$; its effective balance is $t + x$. A token is a certification (an ordinary signature or a trapdoor-preimage relation such as UOV) of a target computed from a semantic message and an opening. *Spending* $d \le t + x$ credits proves in zero knowledge (for instance with VOLE-in-the-head) knowledge of a certified state with an unspent nullifier, reveals the nullifier, and obtains certification of a fresh state with committed credit $t + x - d$; a spent nullifier is rejected thereafter. *Credit conservation* requires that the total credit spent never exceeds the total credit granted by the issuer; *unlinkability* requires that even a malicious issuer cannot link a spend to the issuance or to earlier spends of the same holder beyond what the public amounts reveal.

## Depends on

- [Multi-target and one-more preimage games](../random-oracle-signatures/one-more-preimage-games.md)
- [Zero-knowledge interactive proofs](../zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)
- [Signature scheme](../../security-games/generic-security-games/sig-scheme.md)

## Sources

- Tianyu Zhang, Christopher Patton and Samuel Schlesinger, "VOLE-ACT: anonymous credit tokens from VOLE-in-the-head" (design draft), 2026.
- Carsten Baum et al., "Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from VOLE-in-the-Head", Advances in Cryptology – CRYPTO 2023, Part V, 2023.
