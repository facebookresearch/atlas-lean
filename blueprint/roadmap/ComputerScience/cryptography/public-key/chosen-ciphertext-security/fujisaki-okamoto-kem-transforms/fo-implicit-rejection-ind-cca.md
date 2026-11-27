# IND-CCA security of $\mathrm{FO}^{\not\perp}$ in the random oracle model

Let $\mathrm{PKE}$ be $\delta$-correct with a finite message space $M$ (no spreadness is required). For every IND-CCA adversary $\mathcal{A}$ against the implicit-rejection KEM $\mathrm{FO}^{\not\perp}[\mathrm{PKE}, G, H]$ making at most $q_G$, $q_H$ random-oracle queries and any number of decapsulation queries, there is an IND-CPA adversary $\mathcal{B}$ against $\mathrm{PKE}$ whose running time exceeds that of $\mathcal{A}$ by at most a polynomial in its numbers of queries and the running times of the algorithms of $\mathrm{PKE}$ such that

$$
\mathrm{Adv}^{\mathrm{ind\text{-}cca}}_{\mathrm{FO}^{\not\perp}}(\mathcal{A}) \le (q_G + q_H)\delta + \frac{2 q_G + q_H + 1}{|M|} + 3\,\mathrm{Adv}^{\mathrm{ind\text{-}cpa}}_{\mathrm{PKE}}(\mathcal{B})
$$

(Hofheinz, Hövelmanns and Kiltz, Theorem 3.4 combined with Theorem 3.2, with the errata's correctness term $(q_G + q_P)\delta$ for $q_P \le q_H$ plaintext-checking queries and no validity queries, so that the spreadness term vanishes.) The term $q_H/|M|$ of Theorem 3.4 accounts for random-oracle queries that hit the secret rejection seed. No term depends on the number of decapsulation queries. Asymptotically, for an efficient, IND-CPA-secure, $\delta$-correct word-level PKE family with $\delta$ and $1/|M|$ negligible, $\mathrm{FO}^{\not\perp}$ is IND-CCA secure in the random oracle model against probabilistic polynomial-time adversaries.

## Proof sketch

First replace the implicit-rejection keys $H(s, c)$ by an independent random table, losing $q_H/|M|$. Couple the oracle $H$ on ciphertexts so that decapsulation can be simulated without the secret key (correctness hop, $(q_G + q_H)\delta$), then show the challenge key is uniform unless the challenge plaintext is queried to $G$ or $H$, which is bounded through one-wayness by the IND-CPA advantage.

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

- Dennis Hofheinz, Kathrin Hövelmanns and Eike Kiltz, "A Modular Analysis of the Fujisaki–Okamoto Transformation", Theory of Cryptography (TCC 2017), 2017, Theorems 3.2 and 3.4, with the corrected $\delta$ terms of the errata in Cryptology ePrint Archive, Paper 2017/604.
