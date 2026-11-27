# Hoffman's circulation theorem

Let $D = (V, A)$ be a finite directed graph with real bounds $d \le c$ on the arcs. There is a circulation $f$ with $d \le f \le c$ if and only if $d(\delta^{\mathrm{in}}(U)) \le c(\delta^{\mathrm{out}}(U))$ for every $U \subseteq V$; if $d$ and $c$ are integral and such a circulation exists, an integral one exists. With prescribed net inflows $b_v$, $\sum_v b_v = 0$, a flow with $d \le f \le c$ and $f(\delta^{\mathrm{in}}(v)) - f(\delta^{\mathrm{out}}(v)) = b_v$ exists if and only if $b(S) \le c(\delta^{\mathrm{in}}(S)) - d(\delta^{\mathrm{out}}(S))$ for every $S \subseteq V$, with an integral flow for integral data; this follows by adding one vertex $r$ and, for each $v$, an arc from $v$ to $r$ with both bounds $b_v$ when $b_v \ge 0$ and an arc from $r$ to $v$ with both bounds $-b_v$ when $b_v < 0$. (With net outflows, replace $b$ by $-b$.)

## Sources

- A. Schrijver, *A Course in Combinatorial Optimization*, lecture notes, CWI and University of Amsterdam, 2017, <https://homepages.cwi.nl/~lex/files/dict.pdf>, §4.5, Theorems 4.6 and 4.7
