# Hamming(7,4) codec

The codec on messages in $\mathbb{F}_2^4$ with alphabet $\mathbb{F}_2$: a message is encoded as the list of the seven bits of its Hamming(7,4) codeword. A word of length $7$ is decoded by syndrome decoding it to the nearest codeword and returning the four data bits of that codeword; a word of any other length is rejected.
