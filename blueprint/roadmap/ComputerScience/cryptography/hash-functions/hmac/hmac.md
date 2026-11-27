# HMAC

Let $h : S \times \{0,1\}^n \to S$ be a compression function, $\mathrm{iv} \in S$, $\ell : \mathbb{N} \to \{0,1\}^n$ a length-block map, $L$ a length-field width, $\mathrm{toBits} : S \to \{0,1\}^*$ an arbitrary map from digests to bit strings (no injectivity or canonical serialization is assumed; $S$ need not consist of bit strings), and $\mathrm{ipad}, \mathrm{opad} \in \{0,1\}^n$ two fixed pad blocks. Write $H$ for the [double-length-encoded Merkle–Damgård hash](../a-double-length-encoded-merkle-damg-rd-transform/full-hash.md) of $h$, $\mathrm{iv}$, $\ell$, $L$. For a block-size key $k \in \{0,1\}^n$ and a message $m \in \{0,1\}^*$, **HMAC** (Katz and Lindell, Construction 5.7) is

$$
\mathrm{HMAC}_k(m) = H\bigl((k \oplus \mathrm{opad}) \,\|\, \mathrm{toBits}\bigl(H((k \oplus \mathrm{ipad}) \,\|\, m)\bigr)\bigr),
$$

where $\oplus$ is the [bitwise exclusive or](xor-block.md) of $n$-bit blocks.
