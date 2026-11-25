# Merkle–Damgård padding

For a block length $B$ and a length-field width $L$, the padding of a bit string $M$ is $M$, followed by
a $1$ bit, then the fewest $0$ bits that make the length of the whole padded string, length field
included, a multiple of $B$ (no $0$ bits at all when $B = 0$), then the $L$-bit little-endian encoding
of the length $|M|$: its binary digits from the least significant upward, keeping the $L$ lowest ones.
This has the shape of the strengthened padding used by SHA-2, which writes the length most
significant bit first; Katz and Lindell's Construction 5.3 instead zero-pads the message and appends
its length as one extra block.
