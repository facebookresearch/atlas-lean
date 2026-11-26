# Only the last LZ78 token can omit its symbol

For every finite list $x$, every token of
the LZ78 encoding of $x$ other than the last carries a symbol: an index-only token `(i, none)`
can only be the last token.
