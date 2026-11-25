# Encoded length is the total weighted codeword length

Let $T$ be a coding tree whose leaf
symbols are pairwise distinct. For a symbol $s$, let $\ell(s)$ be the length of the codeword of
$s$ in $T$, or $0$ if $s$ has no codeword. Then the encoded length of $T$ equals
$\sum_{(s, w)} w \cdot \ell(s)$, the sum over the weighted leaves $(s, w)$ of $T$.

Without distinct symbols, the encoder resolves a repeated symbol to its first leaf, and the
encoded length remains the structural weighted path cost.
