# Pointer-jumping PRAM step

One round of Wyllie pointer jumping as a PRAM step with $n$ processors on memory $\mathbb{N} \to \mathbb{N}$, built from the current pointer memory $\mathit{ptr} : \mathbb{N} \to \mathbb{N}$: processor $i$ (for $i < n$) reads cell $\mathit{ptr}(i)$, leaves the value read unchanged, and writes it to cell $i$.

## Sources

- J. C. Wyllie, *The Complexity of Parallel Computations*, PhD thesis, Cornell University, 1979.
