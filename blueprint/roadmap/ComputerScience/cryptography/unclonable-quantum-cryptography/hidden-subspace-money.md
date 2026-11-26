# Public-key quantum money from hidden subspaces relative to a classical oracle

Relative to a classical oracle (providing a serial number and, indexed by it, membership oracles for a random subspace $A\subseteq\mathbb{F}_2^{n}$ of dimension $n/2$ and for $A^{\perp}$), the mini-scheme in which the banknote with serial $s$ is the subspace state $|A_s\rangle$ and verification projects onto $|A_s\rangle$ using the two membership oracles is secure: any counterfeiter making polynomially many queries succeeds with negligible probability. Combined with a digital signature scheme secure against quantum chosen-message attacks (which exists relative to a suitable oracle) through the standard construction, this gives public-key quantum money relative to a classical oracle, unconditionally. In the standard model, Zhandry instantiates the oracles by obfuscation: over $\mathbb{F}=\mathbb{Z}_q$ for a prime $q$, the banknote is $|\psi_S\rangle=|\mathbb{F}|^{-n/4}\sum_{x\in S}|x\rangle$ for a random $S\subseteq\mathbb{F}^{n}$ of dimension $n/2$, its serial number is the pair of programs $(P_0,P_1)=(\mathsf{shO}(S),\mathsf{shO}(S^{\perp}))$, and verification runs $P_0$, applies the quantum Fourier transform, runs $P_1$, and undoes the transform. If $\mathsf{shO}$ is a subspace-hiding obfuscator for $d_0=n/2$ and some $d_1$ with both $|\mathbb{F}|^{n-d_1}$ and $|\mathbb{F}|^{d_1-n/2}$ exponentially large, the scheme is secure; since iO, appropriately padded, is a subspace-hiding obfuscator when injective one-way functions exist, public-key quantum money exists if post-quantum iO and **injective** one-way functions exist.

## Proof sketch

Security relative to the oracle follows from the query lower bound for duplicating subspace states, and the standard construction reduces a counterfeiter of the full scheme to one that breaks either the mini-scheme or the signature scheme. For the obfuscation-based scheme, verification is projective, so a counterfeiter that passes double verification yields a measurement outcome $|\psi_S\rangle\otimes|\psi_S\rangle$. Subspace hiding lets the hybrids replace $\mathsf{shO}(S)$ and $\mathsf{shO}(S^{\perp})$ by obfuscations of random $d_1$-dimensional superspaces $T_0\supseteq S$ and $T_1\supseteq S^{\perp}$, losing only a negligible amount. For fixed such $T_0,T_1$, the programs no longer depend on $S$, which is then a random subspace with $T_1^{\perp}\subseteq S\subseteq T_0$; a no-cloning (no-conversion) bound for this family shows that cloning succeeds with probability at most $2|\mathbb{F}|^{n/2-d_1}$, which is exponentially small.

## Depends on

- [Indistinguishability and virtual black-box obfuscation](../program-obfuscation/indistinguishability-and-virtual-black-box.md)
- [Public-key quantum money and quantum lightning](public-key-quantum-money.md)

## Proof depends on

- [Query lower bound for duplicating subspace states](subspace-state-unclonability.md)

## Sources

- Scott Aaronson, Paul Christiano, "Quantum Money from Hidden Subspaces", STOC (2012), arXiv:1203.4740.
- Mark Zhandry, "Quantum Lightning Never Strikes the Same State Twice", EUROCRYPT (2019).
