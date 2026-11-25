# Gap coding with prefix codes is lossless

Let $L = (d_1 < d_2 < \dots < d_m)$ be a strictly increasing list of positive document identifiers, with gaps $g_1 = d_1$ and $g_k = d_k - d_{k-1}$, all
positive. For each of the variable-byte code, the Elias gamma code and the Golomb code with parameter $b \ge 1$, let $\mathrm{encode}(L)$ be the concatenation
of the codewords of $g_1, \dots, g_m$ and $\mathrm{decode}$ the standard decoder, which reads codewords one at a time and returns the prefix sums. Then
$\mathrm{decode}(\mathrm{encode}(L)) = L$.

## Proof

Each code is prefix-free on the positive integers, so the decoder recovers the codeword sequence, and hence $g_1, \dots, g_m$, uniquely; prefix sums of the
gaps return $d_1, \dots, d_m$.

## Expansion

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: the variable-byte, Elias gamma and Golomb codes with parameter $b \ge 1$ on the positive integers, and their decoders, with the conventions of the cited source.
- Proof prerequisite: these codes are prefix-free on the positive integers (item 3 of [Index construction and postings compression](index-construction-and-postings-compression.md)).
- Proof prerequisite: a prefix-free set of nonempty codewords is uniquely decodable.

## Proof depends on

- [Prefix-free code](../../../InformationTheory/source-coding/prefix-codes/is-prefix-free.md)

## Sources

- J. Zobel and A. Moffat, *Inverted files for text search engines*, ACM Computing Surveys 38(2) (2006), Section 8 (d-gaps; unary, Elias gamma, bytewise and Golomb codes; Figure 10, bytewise encoding and decoding), pp. 19–21.
