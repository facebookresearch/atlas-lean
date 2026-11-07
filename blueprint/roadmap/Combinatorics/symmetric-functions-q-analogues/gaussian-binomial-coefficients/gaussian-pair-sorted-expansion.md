# Ehrenborg–Readdy expansion of the Gaussian coefficient

Let $n$ and $k$ be natural numbers
and let $W$ be the set of words $v = v_0 v_1 \cdots v_{n-1}$ over the alphabet $\{0, 1\}$ with
exactly $k$ letters equal to $1$. For a word $v$, let $\operatorname{inv}(v)$ be the number of
pairs $i < j$ with $v_i > v_j$; call $v$ pair-sorted when $v_{2i} \le v_{2i+1}$ for every $i$
with $2i + 1 < n$; and let $\operatorname{asc}_{\mathrm{odd}}(v)$ be the number of $i$ with
$2i + 1 < n$ and $v_{2i} < v_{2i+1}$. Then, in the polynomial ring $\mathbb{N}[q]$,

$$\sum_{v \in W} q^{\operatorname{inv}(v)} = \sum_{v \in W,\ v \text{ pair-sorted}}
q^{\operatorname{inv}(v)} (1 + q)^{\operatorname{asc}_{\mathrm{odd}}(v)}.$$

The left side is MacMahon's inversion generating polynomial of $W$, which equals the Gaussian
coefficient $\binom{n}{k}_q$. Positions are numbered from $0$, so the pairs $(v_{2i}, v_{2i+1})$
are the source's pairs of positions $(1, 2), (3, 4), \ldots$, and
$\operatorname{asc}_{\mathrm{odd}}$ counts its odd ascents.

## Sources

- Richard Ehrenborg and Margaret A. Readdy, "The Gaussian Coefficient Revisited," Journal of Integer Sequences 19 (2016), Article 16.7.8, Corollary 3 (label corollary_q_1_q), equation (equation_smaller_q_binomial), lines 301–311, https://cs.uwaterloo.ca/journals/JIS/VOL19/Ehrenborg/ehr3.tex
