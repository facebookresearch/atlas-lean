# Block cipher

The algebraic model of a block cipher: a map $E \colon K \to \mathrm{Perm}(X)$ assigning to each key a permutation of the block space $X$, for arbitrary types $K$ and $X$. The forward direction is $E_k$ and the inverse is the inverse permutation $E_k^{-1}$. Katz and Lindell, Section 3.5.1, define block ciphers as keyed permutations of bit strings and require efficient evaluation of $E_k$ and $E_k^{-1}$; this type has neither the bit-string domain nor an efficiency condition.
