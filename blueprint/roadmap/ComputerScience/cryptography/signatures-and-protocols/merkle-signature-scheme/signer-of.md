# Stateful Merkle signer

For Lamport public keys $pk_0, \dots, pk_{N-1}$ and Lamport signing functions
$s_0, \dots, s_{N-1}$, the stateful signer at counter $i < N$ signs a message $m$ with the index $i$,
the key $pk_i$, the Lamport signature $s_i(m)$ and the authentication path of leaf $i$. Once
$i \ge N$ the keys are used up, and it returns nothing.
