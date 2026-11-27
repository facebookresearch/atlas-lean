# Nested continuation hash

Let $h : S \times \{0,1\}^n \to S$, $\ell : \mathbb{N} \to \{0,1\}^n$, a length-field width $L$ and an arbitrary map $\mathrm{toBits} : S \to \{0,1\}^*$ be given, and write $H'_z$ for the [continuation hash](cont-hash.md) from the chaining value $z$. For chaining-value keys $k_{\mathrm{in}}, k_{\mathrm{out}} \in S$ and a message $m$, the nested continuation hash is

$$
H'_{k_{\mathrm{out}}}\bigl(\mathrm{toBits}(H'_{k_{\mathrm{in}}}(m))\bigr).
$$

It has the shape of NMAC (Bellare, Canetti and Krawczyk) but is not NMAC over the full hash, whose keyed hash pads the message alone.
