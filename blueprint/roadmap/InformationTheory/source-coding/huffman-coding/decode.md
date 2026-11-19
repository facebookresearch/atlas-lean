# Decoding a bit string

Let $T$ be a Huffman tree. Decoding the empty bit string with $T$
returns the empty sequence of symbols. To decode a nonempty bit string $w$, decode one codeword
from $w$ with $T$, obtaining a symbol $s$ and the unread bits $w'$, and return $s$ followed by
the decoding of $w'$; decoding fails if decoding one codeword from $w$ fails or if decoding
$w'$ fails.
