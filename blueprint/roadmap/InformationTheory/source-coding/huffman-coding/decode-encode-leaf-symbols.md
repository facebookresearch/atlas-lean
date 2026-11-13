# Decoding inverts encoding

Let $T$ be a Huffman tree and let $s_1, \dots, s_n$
($n \ge 0$) be symbols occurring at leaves of $T$. Encoding $s_1, \dots, s_n$ with $T$ and then
decoding the resulting bit string with $T$, failing if the encoding fails, returns
$s_1, \dots, s_n$. In particular, the encoding succeeds.
