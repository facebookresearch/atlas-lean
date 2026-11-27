# Collision resistance of Merkle-Damgård with n-bit length fields

Let $K$, $S$ and $R$ be types, with decidable equality on the chaining values $S$, let $0 < n$ and $\mathrm{maxLen} + n + n \le n \cdot 2^n$. Take the length-field width $L = n$ and the [block-count length block](../merkle-damg-rd-padding/encode-length.md) $c \mapsto \langle c \rangle_n$. For a keyed compression family $C$ with functions $S \times \{0,1\}^n \to S$, an initial value $\mathrm{iv}$ and a collision finder $A$ for messages in the finite type of bit strings of length strictly less than $\mathrm{maxLen}$ (so both of its candidate messages are shorter than $\mathrm{maxLen}$ bits), with an arbitrary coin distribution,

$$
\mathrm{collAdv}(\mathrm{MD}(C), A) \le \mathrm{collAdv}(C, \mathrm{red}(A)) ,
$$

where $\mathrm{MD}(C)$ is the [keyed full Merkle–Damgård family](md-family.md) on those messages and $\mathrm{red}(A)$ is the [compression-collision reduction](md-reduction.md), both with these parameters. It is [the general bound](coll-advantage-md-family-le.md) with $\mathrm{maxBlocks} = 2^n$ (the argument of Katz and Lindell, Theorem 5.4).
