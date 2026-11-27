# Bitwise instruction tables decompose into small chunk tables

For $W$-bit operands $x,y$ split into $c$ chunks of $W/c$ bits, $x=\sum_{i< c}2^{iW/c}x_i$ and similarly for $y$, the bitwise AND satisfies

$$
\mathrm{AND}(x,y)=\sum_{i=0}^{c-1}2^{iW/c}\,\mathrm{AND}_{W/c}(x_i,y_i),
$$

and likewise for OR and XOR. Hence the table of $\mathrm{AND}$ on $2W$-bit inputs, of size $2^{2W}$, is $c$-decomposable with subtable $\mathrm{AND}_{W/c}$ of size $2^{2W/c}$, whose multilinear extension is $\sum_{j< W/c}2^{j}a_jb_j$ and is evaluable in $O(W/c)$ time.

## Proof sketch

Bitwise operations act independently on each bit position, so they act chunkwise; summing chunk outputs with the appropriate powers of two reassembles the result. The multilinear extension of the chunk table is multilinear in the input bits and agrees with $\sum_j2^{j}a_jb_j$ on Boolean inputs.

## Depends on

- [Decomposable lookup tables](decomposable-table.md)

## Sources

- Arasu Arun, Srinath Setty, Justin Thaler, "Jolt: SNARKs for Virtual Machines via Lookups", EUROCRYPT (2024), IACR ePrint 2023/1217.
- Srinath Setty, Justin Thaler, Riad Wahby, "Unlocking the Lookup Singularity with Lasso", EUROCRYPT (2024), IACR ePrint 2023/1216.
