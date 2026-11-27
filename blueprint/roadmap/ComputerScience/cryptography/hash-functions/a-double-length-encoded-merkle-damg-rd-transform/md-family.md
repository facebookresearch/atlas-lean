# Keyed full Merkle-Damgård hash family

For a keyed compression family $C$ (key generation $\mathrm{gen}_C$, functions $h^s : S \times \{0,1\}^n \to S$), an initial value $\mathrm{iv}$, a length-block map $\ell : \mathbb{N} \to \{0,1\}^n$ and widths $L$, $\mathrm{maxLen}$, the keyed full Merkle–Damgård family has inputs the bit strings shorter than $\mathrm{maxLen}$, and

- key generation $\mathrm{gen}_C$, the key generation of $C$ itself;
- hash: on key $s$, the message $M$ is sent to its [full hash](full-hash.md) with compression function $h^s$, initial value $\mathrm{iv}$, length block $\ell$ and width $L$.

This is a strengthened variant of Katz and Lindell's Construction 5.3.
