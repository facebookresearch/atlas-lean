# The double-length-encoded Merkle–Damgård hash

Let $h : S \times \{0,1\}^n \to S$ be a compression function, $\mathrm{iv} \in S$, $\ell : \mathbb{N} \to \{0,1\}^n$ an arbitrary length-block map (not assumed injective) and $L \in \mathbb{N}$ a length-field width. For a bit string $M$, let $x_1, \dots, x_B$ be its [padded blocks](pad-blocks.md): $M \,\|\, 1 \,\|\, 0 \cdots 0 \,\|\, \langle |M| \rangle_L$ cut into $n$-bit blocks, where the length field keeps the low $L$ bits of $|M|$ little-endian. With $z_0 = \mathrm{iv}$ and $z_i = h(z_{i-1}, x_i)$, **the double-length-encoded Merkle–Damgård hash** of $M$ is

$$
H(M) = h(z_B, \ell(B)) .
$$

So the length enters twice: as $|M| \bmod 2^L$ inside the padding and as the extra block $\ell(B)$ for the block count $B$. The collision theorems assume that $\ell$ separates block counts below a bound; the definition itself does not.

This is a strengthened variant of Katz and Lindell's Construction 5.3, not that construction: Construction 5.3 zero-pads and appends the bit length once.
