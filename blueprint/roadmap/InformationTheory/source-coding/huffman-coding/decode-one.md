# Decoding one codeword

Let $T$ be a Huffman tree and $w$ a bit string, and write $0$ for
the bit false and $1$ for the bit true. If $T$ is a single leaf labelled $s$, decoding one
codeword from $w$ returns $s$ together with the rest of $w$ when $w$ starts with $0$, and fails
otherwise. If $T$ is a fork with left subtree $L$ and right subtree $R$, it fails when $w$ is
empty; when $w$ is a bit $b$ followed by $w'$, it follows $w'$ from the root of $R$ if $b = 1$
and from the root of $L$ if $b = 0$, reading one bit at a time, moving to the left subtree on
$0$ and to the right subtree on $1$, until it reaches a leaf. It then returns the label of that
leaf together with the unread bits, and fails if $w'$ runs out before a leaf is reached.
