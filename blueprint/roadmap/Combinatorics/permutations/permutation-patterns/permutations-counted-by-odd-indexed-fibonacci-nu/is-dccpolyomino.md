# Directed column-convex polyomino

A finite set $S \subseteq \mathbb{Z} \times \mathbb{Z}$ of unit cells is a directed column-convex polyomino (with source cell at the origin) when

- $(0, 0) \in S$;
- every cell $(x, y) \in S$ other than $(0, 0)$ has $(x, y - 1) \in S$ or $(x - 1, y) \in S$;
- every column is contiguous: if $(x, y_1), (x, y_2) \in S$ and $y_1 \le y \le y_2$, then $(x, y) \in S$.

Its area is the number of cells of $S$.

## Sources

- Juan B. Gil, Felix H. Xu, and William Y. Zhu, "Odd-Indexed Fibonacci Numbers via Pattern-Avoiding Permutations", *INTEGERS* 25 (2025), Article A79, Section 5.1.
