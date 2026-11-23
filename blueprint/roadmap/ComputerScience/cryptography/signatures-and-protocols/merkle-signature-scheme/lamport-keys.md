# Lamport public keys of a family of secret keys

For Lamport secret keys $sk_0, \dots, sk_{N-1}$, the $i$-th member of the family of Lamport public
keys is the public key of $sk_i$, obtained by applying the one-way function $f$ to every entry of
$sk_i$.
