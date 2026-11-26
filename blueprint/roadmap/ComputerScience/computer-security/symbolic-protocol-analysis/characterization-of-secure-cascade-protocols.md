# Characterization of secure cascade protocols

A word $\gamma$ of operators has the *balancing property* with respect to a user $A$ if $D_A \in \mathrm{It}(\gamma)$ implies $E_A \in \mathrm{It}(\gamma)$. A [cascade protocol](cascade-protocols.md) is
*balanced* if $\alpha_i(X, Y)$ has the balancing property with respect to $X$ for every $i \ge 2$ and $\beta_i(X, Y)$ has it with respect to $Y$ for every $i \ge 1$.

**Theorem (Dolev and Yao).** A two-party cascade protocol is secure if and only if $\mathrm{It}(N_1(X, Y)) \cap \{E_X, E_Y\} \ne \emptyset$ and the protocol is balanced: the first message is
encrypted under a key of one of the two parties, and no party ever applies its decryption operator in a reply without also applying its encryption operator. Security
is therefore decidable by inspecting the protocol's words.

## Depends on

- [Cascade protocols](cascade-protocols.md)

## Sources

- D. Dolev and A. C. Yao, "On the security of public key protocols", *IEEE Transactions on Information Theory* 29(2):198–208, 1983, copy at <https://www.cs.huji.ac.il/~dolev/pubs/dolev-yao-ieee-01056650.pdf>: Section I (summary of results) and Section II-C, Definitions 4–5, Lemma 1 and Theorem 1 with its proof.
