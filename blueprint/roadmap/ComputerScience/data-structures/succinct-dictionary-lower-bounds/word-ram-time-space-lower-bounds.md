# Word-RAM time–space lower bounds for dynamic succinct dictionaries

Fix $r_{\max}$ and $c_w \ge 1$. Every deterministic or zero-error randomized Word-RAM implementation of the dynamic dictionary with at most $n$ keys of $[U]$ and values in $[V]$, with at most $r_{\max}$ persistent registers, word size $w$ with $\log_2 U / c_w \le w \le c_w \log_2 U$, and memory satisfying $(\mathrm{space} + p)\, w \le \mathrm{OPT}(U, V, n) + R$ (where $p$ is the number of persistent registers), executes in expectation over the insert–query–delete distribution (when $V = 1$, the hard distribution of Li, Liang, Yu and Zhou, Distribution 1, Section 3), and for $V \ge 1$ over some admissible history of at most $4n$ operations as in the cell-probe bounds, at least

- $c \cdot n \cdot k$ instructions when $R \le c_R n \max(\log^{(k)} n, 1)$ and $1 \le k \le \log^* n$,
- $c \cdot n \log_2(n / \max(R,1))$ instructions when $R \le n$,

under the same parameter conditions as the cell-probe bounds, with $c > 0$ depending only on the fixed constants and $r_{\max}$. The update-only bounds transfer in the same way on the insert–delete distribution. This is the transfer of cell-probe lower bounds to the RAM noted by Li, Liang, Yu and Zhou (Section 1, footnote 1): a cell-probe lower bound implies the same time lower bound for RAM.

## Proof sketch

Simulate the Word-RAM implementation by a cell-probe scheme using one extra cell per persistent register; the simulation adds $O(r_{\max})$ probes per operation. Since an implementation must execute at least one non-halting instruction per operation, this overhead is absorbed into the constant, and the cell-probe lower bounds apply. Derived, not stated in this form by the sources: the cell-probe model charges only memory accesses, so the bounds hold over any instruction basis, and, since the potential is nonnegative, they also bound the total potential-amortized cost budget of any Word-RAM implementation certificate.

## Depends on

- [Cell-probe lower bound Ω(k) for dynamic dictionaries with n·log^(k) n redundancy](cell-probe-lower-bound-iterated-log-redundancy.md)
- [Cell-probe lower bound Ω(log(n/R)) for dynamic dictionaries with sublinear redundancy](cell-probe-lower-bound-sublinear-redundancy.md)
- [Update-only cell-probe lower bounds for succinct dictionaries with large values](update-only-cell-probe-lower-bounds.md)
- [Word-RAM implementation certificate with potential-amortized running time](../data-structure-interfaces-and-refinement/word-ram-implementation-certificate.md)
- [Bounded-capacity dictionary specification](../hashing/succinct-dictionaries-and-hash-families/dictionary-specifications/bounded-capacity-dictionary.md)
- [Hard operation distributions for dynamic dictionaries](hard-operation-distributions.md)

## Proof depends on

- [Simulation of Word-RAM data structures by cell-probe schemes](../cell-probe-complexity/word-ram-simulation-by-cell-probe-schemes.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 1842-1862, 2023; arXiv:2306.02253 (Section 1, footnote 1; Distribution 1).
- P. B. Miltersen, "Cell Probe Complexity - a Survey", Advances in Data Structures Workshop (FSTTCS pre-conference workshop), 1999.
