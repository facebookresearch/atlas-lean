# XOR sketches recover a single edge of a vertex cut

Let $G$ be a simple loopless graph on $V = \{1, \dots, n\}$. Give each edge $e = \{u, v\}$ with $u < v$ the name $\mathrm{id}(e) \in \{0, 1\}^{2\lceil \log_2 n \rceil}$ formed by concatenating the $\lceil \log_2 n \rceil$-bit binary encodings of $u - 1$ and $v - 1$ (the label $n$ itself would need $\lceil \log_2 n \rceil + 1$ bits when $n$ is a power of two), so distinct edges get distinct names. For $v \in V$ let $x(v) = \bigoplus_{e \ni v} \mathrm{id}(e)$, the bitwise XOR over incident edges. Then for every $S \subseteq V$,

$$
\bigoplus_{v \in S} x(v) = \bigoplus_{e \in E(S, V \setminus S)} \mathrm{id}(e).
$$

In particular, if $|E(S, V \setminus S)| = 1$, the XOR over $S$ equals the name of the unique cut edge. If moreover each edge is kept independently at levels $j = 0, 1, \dots, \lceil \log_2 n^2 \rceil$ with probability $2^{-j}$, and separate sketches are kept per level, then for any fixed $S$ with $E(S, V \setminus S) \ne \emptyset$, some level has exactly one surviving cut edge with probability at least a positive absolute constant.

## Proof sketch

An edge with both endpoints in $S$ contributes its name twice to the XOR and cancels; an edge with one endpoint in $S$ contributes once. For the sampling claim, if the cut has $c$ edges choose $j$ with $2^{j-1} < c \le 2^{j}$; the number of survivors at level $j$ is $1$ with probability $c \, 2^{-j}(1 - 2^{-j})^{c-1} \ge \frac{1}{2} e^{-1} \cdot (1 - o(1))$. Tree sums of the sketches over Euler-tour trees make the XOR over a tree available in $O(\log n)$ time.

## Proof depends on

- [Euler tour](../euler-tour-tree/tour.md)

## Sources

- Bruce M. Kapron, Valerie King, Ben Mountjoy, "Dynamic graph connectivity in polylogarithmic worst case time", SODA (2013).
