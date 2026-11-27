# The reduction signs like the honest signer

With the public key of a Lamport secret key $sk^*$ planted as the challenge key at index $j$, the
reduction's signing oracle agrees with the honest signer for the family $sk'$ with $sk^*$ at index
$j$: at every index other than $j$, and at index $j$ on every message that $\sigma_j$ signs as the
Lamport signing algorithm under $sk^*$ does.
