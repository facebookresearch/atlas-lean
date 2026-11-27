# Succinctness of indicator-plus-attribute annotation of de Bruijn graphs

**Setting.** A counting (annotated) de Bruijn graph attaches to each pair (k-mer $i$, sample $j$) an
attribute $a_{i,j}$: the number of occurrences of $k$-mer $i$ in experiment $j$, or the set of positions
of $k$-mer $i$ in genome $j$. Most pairs carry no attribute, so the annotation is a sparse $n \times m$
matrix with $s$ nonzero entries taking values in a universe $A$ and all other entries equal to a fixed
zero symbol not in $A$.

**Information-theoretic minimum.** There are $\binom{mn}{s} |A|^{s}$ such matrices, so any encoding needs
at least

$$M^{*}(n, m, s) = \Bigl\lceil \log_2 \Bigl(\tbinom{mn}{s} |A|^{s}\Bigr) \Bigr\rceil \sim \log_2 \tbinom{mn}{s} + s \log_2 |A|$$

bits in the worst case.

**Decomposition.** Store (1) a binary indicator matrix marking the nonzero positions, with a rank
operation on its rows or columns that fixes an order of the nonzero entries, and (2) the attributes in
that order in separate arrays.

**Theorem.** If the indicator matrix and the attribute arrays are each represented succinctly, the
decomposition is a succinct representation of the sparse matrix: it uses $M^{*}(n, m, s)(1 + o(1))$ bits,
and no data structure can represent every such matrix with asymptotically fewer bits. For example,
the indicator matrix reshaped into a bit vector in the Raman-Raman-Rao representation takes
$\log_2 \binom{mn}{s}(1 + o(1))$ bits, and an optimal attribute code takes $s \log_2 |A|$.

The compressed sparse column format is a special case (values array plus column indices and row
delimiters encoding the indicator), so the scheme is never worse than it, while allowing any
rank-supporting compressed binary-relation structure for the indicator and any compressor for the
attributes.

## Depends on

- [Succinct rank and select](../../../../ComputerScience/data-structures/range-query-structures/advanced-data-structures/succinct-rank-and-select.md)

## Expansion

Splitting the matrix into "where" and "what" does not change its entropy: the support is one of
$\binom{mn}{s}$ subsets and, given the support, the values are an arbitrary word in $A^{s}$. Rank on the
indicator converts a position into an index into the attribute array, so lookups remain efficient.
For sequence coordinates the attribute of a successor $k$-mer usually equals its predecessor's plus one,
so a difference transform along graph paths makes the attribute arrays highly compressible before
coding, which is how lossless sequence indexes built this way stay smaller than the gzipped reads.

## Sources

- M. Karasikov, H. Mustafa, G. Rätsch, A. Kahles, "Lossless indexing with counting de Bruijn graphs",
  Genome Research 32 (2022), Methods, Succinctness of the proposed scheme, Theorem 1,
  <https://doi.org/10.1101/gr.276607.122> (PMC9528980).
