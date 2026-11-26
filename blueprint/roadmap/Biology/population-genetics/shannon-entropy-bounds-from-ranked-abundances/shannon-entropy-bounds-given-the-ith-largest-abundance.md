# Shannon entropy bounds given the i-th largest abundance

Let $\mathbf p = (p_1, \dots, p_n)$ with $p_1 \ge \dots \ge p_n \ge 0$, $\sum p_j = 1$, and Shannon entropy $H(\mathbf p) = \sum_j h(p_j)$ with $h(x) = -x\log x$. Fix an index $2 \le i \le n$ and the value $p_i \in [0, 1/i]$ of the $i$-th largest entry.

**Upper bound.** $H$ is maximized by

$$\mathbf p' = \begin{cases} \bigl(\underbrace{p_i, \dots, p_i}_{i}, \underbrace{\tfrac{1 - i p_i}{n-i}, \dots, \tfrac{1 - i p_i}{n-i}}_{n-i}\bigr), & p_i \ge \tfrac1n,\\[4pt] \bigl(\underbrace{\tfrac{1 - (n-i+1)p_i}{i-1}, \dots, \tfrac{1 - (n-i+1)p_i}{i-1}}_{i-1}, \underbrace{p_i, \dots, p_i}_{n-i+1}\bigr), & p_i < \tfrac1n,\end{cases}$$

so

$$H_{\max}(p_i, n) = \begin{cases} i\, h(p_i) + (n-i)\, h\!\left(\dfrac{1 - i p_i}{n-i}\right), & p_i \ge \tfrac1n,\\[6pt] (i-1)\, h\!\left(\dfrac{1 - (n-i+1)p_i}{i-1}\right) + (n-i+1)\, h(p_i), & p_i < \tfrac1n.\end{cases}$$

**Lower bound.** $H$ is minimized by $\mathbf p'' = (1 - (i-1)p_i, p_i, \dots, p_i, 0, \dots, 0)$ with $i-1$ entries equal to $p_i$, so

$$H_{\min}(p_i, n) = h\bigl(1 - (i-1)p_i\bigr) + (i-1)\, h(p_i).$$

As $p_i \to 1/i$ both bounds approach $\log i$. For $i = 2$ and $p_2 \to 1/2$ the entropy is forced to $\log 2$.

## Depends on

- [Shannon entropy bounds given the largest abundance](shannon-entropy-bounds-given-the-largest-abundance.md)

## Expansion

As for the largest abundance, the proof combines Schur-concavity of $H$ with majorization. Among ordered vectors with $i$-th entry $p_i$, $\mathbf p'$ (all entries as equal as the ordering and the unit sum allow) is majorized by every other vector, and $\mathbf p''$ (entries $2, \dots, i$ equal to $p_i$ and all remaining mass on the first entry) majorizes every other vector. The case split at $p_i = 1/n$ records whether the entries after the $i$-th or before it absorb the leftover mass. For $n = 3$ the bounds for fixed $p_1$ and fixed $p_2$ coincide where they share a single free variable, a consistency check given in the source.

## Sources

- M. L. Morrison and N. A. Rosenberg, "Mathematical bounds on Shannon entropy given the abundance of the ith most abundant taxon", *Journal of Mathematical Biology* 87 (2023), article 76, <https://doi.org/10.1007/s00285-023-01997-3> (PMC10603011; Theorems 3 and 4, Equations (4) and (5), proofs in Appendix A).
