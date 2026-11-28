# Packed additively homomorphic encryption

*Packed additively homomorphic encryption* (PAHE) is the interface used by Gazelle for linear layers: a private-key encryption scheme on vectors in $\mathbb{Z}_p^n$ with slotwise addition of ciphertexts, slotwise multiplication by a plaintext vector and a fixed group of slot permutations, which is CPA secure against efficient adversaries.

Plaintexts are vectors $u\in\mathbb{Z}_p^n$. A PAHE scheme has key generation, randomized encryption $u\mapsto[u]$ and deterministic decryption under a secret key, and evaluation algorithms

- $\mathrm{SIMDAdd}([u],[v])$, an encryption of $u+v$;
- $\mathrm{SIMDScMult}([u],v)$ for a plaintext $v\in\mathbb{Z}_p^n$, an encryption of the slotwise product $u\circ v$;
- $\mathrm{Perm}([u],\pi)$ for $\pi$ in a fixed group of primitive permutations, an encryption of $u_\pi=(u_{\pi(1)},\dots,u_{\pi(n)})$;

each correct on ciphertexts within the scheme's decryption budget. The interface uses no product of two ciphertexts. Security: for every efficient adversary the CPA advantage of the private-key scheme is negligible in the security parameter. In the lattice instantiations of the source, $n=\varphi(m)$ for a cyclotomic order $m$, slotwise products need $p\equiv1\pmod m$, and the permutation group is all cyclic rotations when $m$ is prime and the half-rotations $C_{n/2}\times C_2$ when $m=2^k\ge8$.

## Depends on

- [CPA advantage](../../security-games/generic-security-games/cpa-advantage.md)
- [Efficient adversaries](../../security-games/asymptotic-security/efficient-adversaries.md)
- [Negligible advantage](../../security-games/asymptotic-security/negligible-adv.md)

## Proof depends on

None.

## Expansion

A definition. The source additionally requires a function-privacy property of evaluated ciphertexts, stated informally; it is not part of this interface, and a precise version is a separate page.

## Sources

- Chiraag Juvekar, Vinod Vaikuntanathan, Anantha Chandrakasan, "GAZELLE: A Low Latency Framework for Secure Neural Network Inference", 27th USENIX Security Symposium (2018), [USENIX copy](https://www.usenix.org/conference/usenixsecurity18/presentation/juvekar); preprint arXiv:1801.05507v1. Section 3 (3.1–3.4).
