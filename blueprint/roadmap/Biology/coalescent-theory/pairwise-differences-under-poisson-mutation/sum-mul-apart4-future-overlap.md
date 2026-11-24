# Mean remaining path overlap of two pairs from four distinct lineages

Let `a`, `b`, `c`, `d` be genes of a sample of `n` genes with `a ≠ b`, `a ≠ c`, `a ≠ d`,
`b ≠ c` and `c ≠ d`, let `t ≤ n - 1`, and let `Y` be a real function on the
[ranked labeled histories](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md)
of the sample that [depends only on their first `t` steps](depends-before.md). For a history
`h`, let `A(h)` be `1` if the four genes are in [four distinct lineages](apart4.md) after the
first `t` events of `h` and `0` otherwise, and let `F(h) = ∑_{t ≤ u < n - 1} N_u(h) / C(n - u, 2)`
be the [expected remaining overlap](future-overlap.md) of the paths of `{a, b}` and `{c, d}`,
where `N_u(h)` is the number of lineages after `u` events that hold exactly one of `a, b` and
exactly one of `c, d`, and `C(m, 2) = m (m - 1) / 2`. Then, summing over all ranked labeled
histories of the sample,

`∑_h Y(h) A(h) F(h) = (2/3) ∑_h Y(h) A(h)`.

If `b = d`, the four genes are never in four distinct lineages and both sides are `0`.

[Random joining](../ranked-labeled-histories-of-coalescent-trees/random-joining.md) gives every
history the same probability, so this says: given the first `t` steps, if the four genes are
then in four distinct lineages, the remaining overlap of the two paths has mean `2/3`. Nothing
overlaps while the four lineages stay distinct. The first merger among them joins one of the
four cross pairs `{a, c}`, `{a, d}`, `{b, c}`, `{b, d}` with probability `4/6`, and the overlap
is then that of two pairs through a shared lineage, of mean `1`; if `{a, b}` or `{c, d}` merges
first, nothing overlaps.
