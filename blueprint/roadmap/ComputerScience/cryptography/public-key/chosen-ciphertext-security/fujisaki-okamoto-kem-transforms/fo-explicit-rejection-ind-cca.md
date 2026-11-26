# IND-CCA security of $\mathrm{FO}^{\perp}$ in the random oracle model

Let $\mathrm{PKE}$ be $\delta$-correct and $\gamma$-spread with a finite message space $M$. For every IND-CCA adversary $\mathcal{A}$ against $\mathrm{FO}^{\perp}[\mathrm{PKE}, G, H]$ making at most $q_G$, $q_H$ random-oracle queries and $q_D$ decapsulation queries, there is an IND-CPA adversary $\mathcal{B}$ against $\mathrm{PKE}$ whose running time exceeds that of $\mathcal{A}$ by at most a polynomial in its numbers of queries and the running times of the algorithms of $\mathrm{PKE}$ such that

$$
\mathrm{Adv}^{\mathrm{ind\text{-}cca}}_{\mathrm{FO}^{\perp}}(\mathcal{A}) \le (q_G + q_H) \delta + q_D 2^{-\gamma} + \frac{2 q_G + 1}{|M|} + 3\,\mathrm{Adv}^{\mathrm{ind\text{-}cpa}}_{\mathrm{PKE}}(\mathcal{B})
$$

(a correctness term, a spreadness term, a guessing term and three times the IND-CPA advantage). This is Hofheinz, Hövelmanns and Kiltz, Theorem 3.2, with the errata's correctness term $(q_G + q_P)\delta$, applied to the one-wayness adversary of Theorem 3.3, which makes at most $q_H$ plaintext-checking queries and one validity query for each decapsulation query (Figures 10 and 11). Their Section 3.3 states the simplified bound $q_{RO}\,\delta + q_{RO}\,2^{-\gamma} + 3q_{RO}/|M| + 3\,\mathrm{Adv}^{\mathrm{ind\text{-}cpa}}_{\mathrm{PKE}}$ with $q_{RO} = q_G + q_H$.

Asymptotically: if a word-level PKE family is efficient, IND-CPA secure, $\delta$-correct and $\gamma$-spread with $\delta$, $2^{-\gamma}$ and $1/|M|$ negligible, then $\mathrm{FO}^{\perp}$ is IND-CCA secure in the random oracle model against probabilistic polynomial-time adversaries.

## Proof sketch

Replace decapsulation by a keyless simulator that answers from the random-oracle cache: the spreadness term covers ciphertexts the adversary did not derive from a $G$-query, and the correctness term covers decryption failures. Then the challenge key is independent of everything unless the adversary queries the challenge message, an event bounded via one-wayness, which in turn is bounded by IND-CPA advantage plus $1/|M|$.

## Depends on

- [The KEM transforms $U^{\perp}$ and $U^{\not\perp}$ and the Fujisaki–Okamoto KEMs](transforms-u-and-fo-kems.md)
- [Public-key encryption with explicit coins, $\delta$-correctness and $\gamma$-spreadness](pke-with-explicit-coins.md)
- [CPA experiment for key encapsulation](../../key-encapsulation-and-hybrid-encryption/kem-game.md)
- [The random oracle model](../../random-oracle-constructions/the-random-oracle-model.md)
- [Negligible advantage](../../../security-games/asymptotic-security/negligible-adv.md)

## Proof depends on

- [Correctness of the Fujisaki–Okamoto KEMs](fo-kem-correctness.md)
- [Lazy and eager sampling of a random oracle are equivalent](lazy-eager-random-oracle.md)
- [The difference lemma](../../../security-games/games-and-advantages/advantage-le-win-prob-of-eq-of-not-bad.md)

## Sources

- Dennis Hofheinz, Kathrin Hövelmanns and Eike Kiltz, "A Modular Analysis of the Fujisaki–Okamoto Transformation", Theory of Cryptography (TCC 2017), 2017, Theorems 3.2 and 3.3 and Section 3.3, with the corrected $\delta$ terms of the errata in Cryptology ePrint Archive, Paper 2017/604.
