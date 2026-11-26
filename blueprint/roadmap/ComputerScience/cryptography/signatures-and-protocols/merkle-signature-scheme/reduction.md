# Reduction from Merkle forgeries to Lamport forgeries

The reduction is a Lamport one-time forger with coins $(j, sk', r)$: a guessed index, a family of
Lamport secret keys and the Merkle forger's coins. It plants the challenge Lamport public key at
leaf $j$, uses its own keys at the other leaves, answers the $j$-th signing query with its single
Lamport signing query, and outputs the Lamport part of the forgery.
