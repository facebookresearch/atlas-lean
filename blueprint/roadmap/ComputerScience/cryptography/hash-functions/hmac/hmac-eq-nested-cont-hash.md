# HMAC in nested form

Let $h : S \times \{0,1\}^n \to S$ be a compression function, $\mathrm{iv} \in S$, $\ell : \mathbb{N} \to \{0,1\}^n$ a length-block map, $L$ a length-field width, $\mathrm{toBits} : S \to \{0,1\}^*$ an arbitrary map from digests to bit strings (no injectivity or canonical serialization is assumed; $S$ need not consist of bit strings), and $\mathrm{ipad}, \mathrm{opad} \in \{0,1\}^n$ two fixed pad blocks. Write $H$ for the [double-length-encoded Merkle–Damgård hash](../a-double-length-encoded-merkle-damg-rd-transform/full-hash.md) of $h$, $\mathrm{iv}$, $\ell$, $L$. Let $0 < n$. For every key $k \in \{0,1\}^n$ and message $m$, with the [derived keys](inner-key.md) $k_{\mathrm{in}} = h(\mathrm{iv}, k \oplus \mathrm{ipad})$ and $k_{\mathrm{out}} = h(\mathrm{iv}, k \oplus \mathrm{opad})$,

$$
\mathrm{HMAC}_k(m) = H'_{k_{\mathrm{out}}}\bigl(\mathrm{toBits}(H'_{k_{\mathrm{in}}}(m))\bigr),
$$

where $H'_z$ is the [continuation hash](cont-hash.md) from $z$ (Katz and Lindell, Section 5.3.2).
