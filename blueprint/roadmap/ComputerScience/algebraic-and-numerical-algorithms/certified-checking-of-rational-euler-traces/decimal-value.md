# Positional value of a run of digits

For a list of characters `d_1 … d_k`, most significant first, the positional value is the natural
number `∑_i v(d_i) 10^{k-i}`, with `v` the [digit value](digit-value.md); it is `0` for the empty
list, and leading zeros add nothing.
