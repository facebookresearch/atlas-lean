# Unclonable encryption from BB84 states via monogamy

Let $F=\{f_\lambda:\{0,1\}^{\lambda}\times\{0,1\}^{\lambda}\to\{0,1\}^{n(\lambda)}\}$ be a quantum-secure pseudorandom function. *$F$-conjugate encryption* has key $(s,\theta)\in\{0,1\}^{\lambda}\times\{0,1\}^{\lambda}$ and encrypts $m\in\{0,1\}^{n}$ by sampling a fresh uniform $x\in\{0,1\}^{\lambda}$ and outputting the classical string $c=m\oplus f_\lambda(s,x)$ together with the BB84 state $|x\rangle_\theta$. In the cloning experiment, $m$ is uniform; an adversary $\mathcal{A}$ maps the ciphertext to a state on two registers, which go to non-communicating parties $\mathcal{B},\mathcal{C}$; each then receives $\theta$ and, with the qPRF modeled as an oracle, quantum oracle access to $f_\lambda(s,\cdot)$ instead of $s$; they win if both output $m$. Every such attack with polynomially many queries wins with probability at most $9\cdot2^{-n}+\mathrm{negl}(\lambda)$, i.e. the scheme is $\log_2 9$-uncloneable secure. The term $9\cdot2^{-n}$ cannot be dropped, since guessing already wins with probability $2^{-n}$ (one half for a one-bit message), so the bound is negligible only when $n(\lambda)=\omega(\log\lambda)$. This is distinct from *conjugate encryption*, which has key $(r,\theta)\in\{0,1\}^{\lambda}\times\{0,1\}^{\lambda}$, encrypts $m\in\{0,1\}^{\lambda}$ as $|m\oplus r\rangle_\theta$ with no oracle, and gives the two parties, once both know $(r,\theta)$, success probability at most $\bigl(\tfrac12+\tfrac1{2\sqrt2}\bigr)^{\lambda}$ on a uniform message.

## Proof sketch

For conjugate encryption, averaging over $m$ moves the pad $r$ into the winning projector, and the bound is the BB84 monogamy bound. For $F$-conjugate encryption, replace $f_\lambda(s,\cdot)$ by a uniformly random function $H$, which changes the winning probability negligibly by qPRF security; averaging over $m$ again moves $H(x)$ into the projector. An oracle lemma adapted from the one-way-to-hiding technique bounds the winning probability by $9\cdot2^{-n}+(3q_{\mathcal{B}}q_{\mathcal{C}}+2)q_{\mathcal{B}}q_{\mathcal{C}}\sqrt{M}$ for $q_{\mathcal{B}},q_{\mathcal{C}}$ queries, where $M$ is the probability that measuring the query registers of both parties at random query times yields $x$ for both; the BB84 monogamy bound makes $M$ exponentially small in $\lambda$.

## Depends on

- [Unclonable encryption](unclonable-encryption.md)
- [The quantum random oracle model](../security-games/quantum-random-oracle-techniques/quantum-random-oracle-model.md)

## Proof depends on

- [Monogamy-of-entanglement game for BB84 states](monogamy-bb84.md)
- [One-way to hiding lemma for reprogramming quantum random oracles](../security-games/quantum-random-oracle-techniques/one-way-to-hiding.md)

## Sources

- Anne Broadbent, Sébastien Lord, "Uncloneable Quantum Encryption via Oracles", TQC (2020).
