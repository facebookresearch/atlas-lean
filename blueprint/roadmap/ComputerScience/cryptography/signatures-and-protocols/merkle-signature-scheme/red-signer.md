# The reduction's signing oracle

The reduction's stateful signer uses its Lamport public keys and signs at index $j$ with a given
function $\sigma_j$, and at every other index $i$ with the Lamport signing algorithm under $sk'_i$.
