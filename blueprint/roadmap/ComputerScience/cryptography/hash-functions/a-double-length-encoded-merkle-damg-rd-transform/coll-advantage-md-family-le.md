# Collision resistance of the full Merkle-Damgård hash family

Let $K$, $S$ and $R$ be types, with decidable equality on the chaining values $S$, and let $0 < n$. Let $C$ be a keyed compression family with keys in $K$ and functions $S \times \{0,1\}^n \to S$, let $\mathrm{iv} \in S$, let $\ell : \mathbb{N} \to \{0,1\}^n$ separate block counts below $\mathrm{maxBlocks}$ ($\ell(a) = \ell(b)$ with $a, b < \mathrm{maxBlocks}$ implies $a = b$), and let $\mathrm{maxLen} + L + n \le n \cdot \mathrm{maxBlocks}$. Then for a collision finder $A$ for messages in the finite type of bit strings of length strictly less than $\mathrm{maxLen}$ (so both of its candidate messages are shorter than $\mathrm{maxLen}$ bits), with an arbitrary coin distribution,

$$
\mathrm{collAdv}(\mathrm{MD}(C), A) \le \mathrm{collAdv}(C, \mathrm{red}(A)) ,
$$

where $\mathrm{MD}(C)$ is the [keyed full Merkle–Damgård family](md-family.md) on those messages and $\mathrm{red}(A)$ is the [compression-collision reduction](md-reduction.md). The length bound is a domain restriction on $A$, not a numerical side condition on an otherwise arbitrary finder. This is the argument of Katz and Lindell, Theorem 5.4, for this variant.
