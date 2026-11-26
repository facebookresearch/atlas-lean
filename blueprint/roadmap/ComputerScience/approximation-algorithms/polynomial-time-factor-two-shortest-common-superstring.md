# Polynomial-time factor-two approximation for shortest common superstring

A symbol is a finite bit string, a word is a finite list of symbols, and the input $S$ is a finite list of words. Let $\mathrm{opt}(S)$ be the least symbol length of a word containing each member of $S$ as a contiguous substring. There is one deterministic function $f$ such that for every $S$, $f(S)$ contains every input word as a contiguous substring and its symbol length is at most $2\mathrm{opt}(S)$. Empty words count as substrings and neither distinctness nor a substring-free promise is assumed.

The function has a deterministic finite-stack implementation with each stack alphabet finite, in time polynomial in the encoded input bit length. At each list layer (bits in a symbol, symbols in a word, and words in an instance), the encoding prefixes each element's code by a zero and ends the list with a one; an atomic Boolean is encoded by itself. The output uses the word encoding. The ratio is measured in symbols, not encoded bits.

## Depends on

- The contiguous substring predicate, symbol-length optimum and nested bit encoding above.

## Proof depends on

- A factor-two construction with an unrestricted optimum comparison, and a bit-length implementation of all string operations on nested encodings.

## Expansion

Bridge the substring predicate to the native word model and show the unbounded symbol alphabet has an explicit finite-bit implementation. Isolate the approximation proof and polynomial-time compilation. This result does not assert that greedy maximal-overlap merging achieves factor two.

## Sources

- OpenAI, [Superstring.lean, definitions and `main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Superstring.lean#L7-L39).
