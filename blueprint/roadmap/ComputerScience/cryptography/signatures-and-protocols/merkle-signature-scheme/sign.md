# Merkle signing

The stateful signing algorithm signs a message $m$ at counter $i < N$ with the $i$-th Lamport key: the
signature consists of $i$, the Lamport public key of $sk_i$, the Lamport signature on $m$ under
$sk_i$, and the authentication path of leaf $i$. Once the $N$ keys are used up, it returns nothing.
