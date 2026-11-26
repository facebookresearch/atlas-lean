# Hamming(7,4) codec on a seven-bit word

For every seven-bit word $y$, the [Hamming(7,4) codec](encoding.md) returns the four data bits of the syndrome-decoded word of $y$. This is the transmitted message only when at most one bit was flipped ([recovery from one error](../hamming-7-4-code/decode-add.md)); with two or more errors the decoder can return a different message.
