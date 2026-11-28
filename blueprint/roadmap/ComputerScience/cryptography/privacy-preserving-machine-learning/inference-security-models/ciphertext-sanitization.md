# Ciphertext sanitization

A *sanitization algorithm* for an encryption scheme is a public randomized map $\mathsf{Sanitize}(pk,\cdot)$ on ciphertexts that, for all but a small fraction of generated keys, preserves decryption and sends any two ciphertexts with the same decryption to distributions within statistical distance $2^{-\lambda}$, even given the secret key.

Let $(\mathsf{KeyGen},\mathsf{Enc},\mathsf{Dec})$ be a public-key encryption scheme with public key space $\mathcal{P}$ and ciphertext space $\mathcal{C}$ and message space $\mathcal{M}$. The source treats decryption as a map to $\mathcal{M}$; for a scheme whose decryption may output $\bot$, both conditions below range only over ciphertexts that decrypt to messages, and nothing is required of rejecting ciphertexts. A polynomial-time randomized algorithm $\mathsf{Sanitize}:\mathcal{P}\times\mathcal{C}\to\mathcal{C}$ is

- *message-preserving* if, with probability at least $1-\lambda^{-\omega(1)}$ over $(pk,sk)\leftarrow\mathsf{KeyGen}(1^\lambda)$, every $c\in\mathcal{C}$ with $\mathsf{Dec}(sk,c)\in\mathcal{M}$ satisfies $\mathsf{Dec}(sk,\mathsf{Sanitize}(pk,c))=\mathsf{Dec}(sk,c)$;
- *(statistically) sanitizing* if, with probability at least $1-2^{-\lambda}$ over $(pk,sk)\leftarrow\mathsf{KeyGen}(1^\lambda)$, every $c,c'\in\mathcal{C}$ with $\mathsf{Dec}(sk,c)=\mathsf{Dec}(sk,c')\in\mathcal{M}$ satisfy

$$
\Delta\big(\mathsf{Sanitize}(pk,c)\,|\,(pk,sk),\ \mathsf{Sanitize}(pk,c')\,|\,(pk,sk)\big)\le 2^{-\lambda} .
$$

Both quantifiers over ciphertexts sit inside the high-probability event over keys. For a homomorphic scheme the source draws the consequence that, outside the bad-key event, sanitized outputs of evaluating two circuits on honestly formed keys and ciphertexts are statistically close whenever they decrypt to the same plaintext. This is weaker than [circuit privacy](homomorphic-circuit-privacy.md) in Gentry's sense, which quantifies over every generated key pair.

## Depends on

- [Public-key encryption scheme](../../security-games/generic-security-games/pkescheme.md)
- [Statistical indistinguishability of distribution ensembles](../../security-games/computational-indistinguishability-of-ensembles/statistical-indistinguishability-of-ensembles.md)

## Proof depends on

None.

## Expansion

A definition. Ducas and Stehlé's realization, a separate result, iterates $\mathsf{Wash}(pk,c)=\mathsf{Rerand}(pk,\mathsf{Refresh}(pk,c))$ $\kappa$ times. With $\mathcal{C}_\mu$ the ciphertexts decrypting to $\mu$ and $\mathcal{C}^*_\mu=\mathsf{Refresh}(pk,\mathcal{C}_\mu)$, their Theorem 3.3 assumes their Eq. (1), that $\mathsf{Rerand}(pk,c)\in\mathcal{C}_\mu$ for every $c\in\mathcal{C}^*_\mu$, and that $\Delta(\mathsf{Rerand}(pk,c),\mathsf{Rerand}(pk,c'))\le\delta$ for all $\mu$ and all $c,c'\in\mathcal{C}^*_\mu$, and concludes $\Delta(\mathsf{Sanitize}(pk,c),\mathsf{Sanitize}(pk,c'))\le\delta^\kappa$; when Eq. (1) holds only with overwhelming probability the source adds an error term (after Lemma 3.2).

## Sources

- Léo Ducas, Damien Stehlé, "Sanitization of FHE Ciphertexts", EUROCRYPT 2016, LNCS 9665, pp. 294–310, DOI 10.1007/978-3-662-49890-3_12, [publisher chapter](https://link.springer.com/chapter/10.1007/978-3-662-49890-3_12); same numbering in the authors' [IACR ePrint 2016/164](https://eprint.iacr.org/2016/164): §1, §2 (every ciphertext decrypts to a message), §3 Definition 3.1, §3.1 Eq. (1) and Lemma 3.2, §3.2 Theorem 3.3.
