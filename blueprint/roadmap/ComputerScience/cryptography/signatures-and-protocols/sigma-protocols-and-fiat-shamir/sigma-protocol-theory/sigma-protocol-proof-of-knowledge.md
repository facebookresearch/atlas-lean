# Special-sound Sigma protocols are proofs of knowledge with a PPT rewinding extractor

Let $\Pi$ have efficient special soundness and challenge set $C$. There is a strict probabilistic polynomial-time knowledge extractor which, given rewinding access to any prover $P^*$, runs it twice with the same coins and independent uniform challenges and applies the special-soundness extractor. If $P^*$ convinces the verifier on statement $y$ with probability $\varepsilon$, the extractor outputs a witness with probability at least

$$
\varepsilon^2 - \frac{\varepsilon}{|C|},
$$

and the same bound holds on average over any distribution of statements. Hence a special-sound Sigma protocol with superpolynomially large challenge space is a proof of knowledge with knowledge error $1/|C|$ (after repetition, negligible).

## Proof sketch

Apply the rewinding lemma to the prover's coins and the challenge: two accepting runs with distinct challenges occur with probability at least $\varepsilon^2 - \varepsilon/|C|$.

## Depends on

- [Efficient special soundness, efficient special HVZK and computational special HVZK](efficient-sigma-protocol-notions.md)
- [Knowledge soundness](../../zero-knowledge-and-arguments/knowledge-soundness.md)

## Proof depends on

- [The rewinding lemma](../../zero-knowledge-and-arguments/the-rewinding-lemma.md)

## Sources

- Mihir Bellare and Gregory Neven, "Multi-Signatures in the Plain Public-Key Model and a General Forking Lemma", Proceedings of the 13th ACM Conference on Computer and Communications Security (CCS 2006), ACM, 2006, pp. 390–399, Lemma 1.
- Thomas Attema, Ronald Cramer and Lisa Kohl, "A Compressed Σ-Protocol Theory for Lattices", Advances in Cryptology – CRYPTO 2021, Springer, 2021, Corollary 1.
