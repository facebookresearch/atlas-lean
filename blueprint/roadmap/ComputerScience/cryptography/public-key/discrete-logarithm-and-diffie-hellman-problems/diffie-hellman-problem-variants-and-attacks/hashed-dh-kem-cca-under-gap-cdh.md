# The hashed Diffie–Hellman KEM is CCA secure in the random oracle model under gap-CDH

Let the KEM have public key $u = g^{\alpha}$, encapsulate by choosing $\beta$, sending $v = g^\beta$ and deriving the key $H(v, u^\beta)$, and decapsulate by $H(v, v^\alpha)$, where $H$ is a random oracle. Under gap-CDH this KEM is IND-CCA secure.

## Proof sketch

The reduction embeds the challenge in $u$ and $v^*$ and answers hash queries lazily. It answers decapsulation queries without $\alpha$ by keeping the hash table consistent: for a query $v$, it searches its table for an entry $(v, w)$ with $(u, v, w)$ a DH triple using the DDH oracle, and otherwise assigns a random key and patches later. The challenge key is distinguishable only if the adversary queries $H(v^*, [u, v^*])$, which yields the CDH solution.

## Depends on

- [Gap computational Diffie–Hellman assumption](gap-cdh-assumption.md)
- [CPA experiment for key encapsulation](../../key-encapsulation-and-hybrid-encryption/kem-game.md)
- [The random oracle model](../../random-oracle-constructions/the-random-oracle-model.md)

## Proof depends on

- [Fundamental lemma of game playing for stateful oracle handlers](../../../security-games/identical-until-bad-oracle-handlers/fundamental-lemma-for-stateful-handlers.md)

## Sources

- M. Abdalla, M. Bellare and P. Rogaway, "The Oracle Diffie-Hellman Assumptions and an Analysis of DHIES", Topics in Cryptology (CT-RSA 2001), LNCS 2020, 2001.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
