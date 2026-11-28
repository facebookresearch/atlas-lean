# Matrix multiplication algorithms

- [Rectangular matrix accumulation](rectangular-matrix-accumulate.md)
- [Square matrix accumulation](matrix-accumulate.md)
- [Entries of rectangular matrix accumulation](rectangular-matrix-accumulate-apply.md)
- [Rectangular matrix accumulation computes $C + AB$](rectangular-matrix-accumulate-ret.md)
- [Operation count of rectangular matrix accumulation](rectangular-matrix-accumulate-time.md)
- [Rectangular matrix accumulation with zero inner dimension](rectangular-matrix-accumulate-zero-inner.md)
- [Square matrix accumulation computes $C + AB$](matrix-accumulate-ret.md)
- [Operation count of square matrix accumulation](matrix-accumulate-time.md)
- [Recursive matrix multiply-accumulate](recursive-matrix-accumulate.md)
- [Entries of the recursive matrix multiply-accumulate](recursive-matrix-accumulate-apply.md)
- [Correctness of the recursive matrix multiply-accumulate](recursive-matrix-accumulate-ret.md)
- [Operation count of the recursive matrix multiply-accumulate](recursive-matrix-accumulate-time.md)

## Related topics

- [Communication lower bounds](../communication-lower-bounds/README.md): every algorithm that evaluates all $n^3$ products, in any order, moves $\Omega(n^3/\sqrt{M})$ words through a fast memory of $M$ words; blocked and recursive orders attain this.
- [Rounding error analysis](../rounding-error-analysis/README.md): the entrywise error bound $\gamma_n |A|\,|B|$ of the floating-point product.
- [Leverage scores](leverage-scores/README.md)
