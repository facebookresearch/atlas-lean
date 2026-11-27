# Continuation hash

Let $h : S \times \{0,1\}^n \to S$, $\ell : \mathbb{N} \to \{0,1\}^n$ and a length-field width $L$ be given. For a chaining value $z \in S$ and a bit string $m$, let $T$ be the list of $n$-bit blocks of the [padding of $m$ behind an $n$-bit prefix](pad-tail.md), $m \,\|\, 1 \,\|\, 0 \cdots 0 \,\|\, \langle n + |m| \rangle_L$, whose length field records $(n + |m|) \bmod 2^L$. The **continuation hash** is

$$
H'_z(m) = h\bigl(\mathrm{chain}_z(T),\ \ell(|T| + 1)\bigr),
$$

where $\mathrm{chain}_z$ runs $h$ over $T$ from $z$. The blocks of $T$ are padded continuation blocks, and the block count includes the one block before $m$. For $0 < n$ this is how the full hash finishes a message after a leading $n$-bit block ([hashing a one-block prefix](full-hash-vector-append.md)). It is not the full hash started at $z$, which pads $m$ alone.
