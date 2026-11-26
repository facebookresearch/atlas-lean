# LZ78 decoding

The LZ78 decoding of a list of tokens reads them in order with a dictionary
that starts empty. A token `(i, s)` whose index `i` is at most the number of tokens before it is
decoded to the empty phrase (`i = 0`) or the `i`-th decoded phrase, followed by the symbol `a`
when `s = some a`; the decoded phrase becomes the next dictionary entry. The result is the
concatenation of the decoded phrases, or `none` when some token's index exceeds the number of
tokens before it. Decoding does not check that the tokens are ones `LZ78.encode` emits: it
accepts an index-only token `(i, none)` at any position, decoding it to the phrase at index `i`
and adding a copy of that phrase to the dictionary, and a token whose phrase is already in the
dictionary.
