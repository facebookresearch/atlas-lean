# Decoding an encoded trace

For a list of characters `s`, the trace decoder returns, when `s` has at most 300 characters and
[splits](split-on-char.md) at `,` into exactly eleven pieces that all
[decode as tokens](decode-token.md), the list of the eleven token values; otherwise it returns
nothing.
