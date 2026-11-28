# Domain and degree identities for smooth FRI

In smooth FRI with initial domain size $2^d$, $m$ rounds of folding arities $l^{(i)} = 2^{s_i}$ and initial dimension $k_0 \le 2^d$, let $c_i = s_0 + \dots + s_{i-1}$, and assume that $k_0$ is a positive multiple of $2^{c_m}$. Then the round domains and dimensions satisfy $2^{c_i}\, n_i = 2^d$ and $2^{c_i} k_i = k_0$, every dimension is at least $1$, and the curve-degree budgets telescope exactly:

$$
\sum_{i=0}^{m-1} (l^{(i)} - 1)\, n_{i+1} = 2^d - 2^{d - c_m},
$$

with every round's budget at most the round-$0$ budget $(l^{(0)} - 1) n_1$. Moreover, for every round $i$ and coordinate $j$ of the active domain, the number of starting points of the query phase that pass through $j$ equals $2^{c_i}$ (exact starting-point counting), and, when $m \ge 1$, for a prefix of length $m$ and any final oracle, the number of starting points that pass all consistency checks is at most $2^{c_m}$ times the number of positions of $D_m$ where the folded word $\mathrm{Fold}(f^{(m-1)}, z_{m-1})$ agrees with the final codeword; equivalently, the fraction of starting points that pass is at most the fraction of agreement positions in $D_m$.

## Proof sketch

$(l - 1) n_{i+1} = n_i - n_{i+1}$, so the sum telescopes. Each point of $D_i$ is the image of exactly $2^{c_i}$ points of $D_0$ under the folding maps. A starting point that passes the last consistency check maps to a position of $D_m$ where the fold agrees with the final codeword, and each such position has exactly $2^{c_m}$ starting points above it.

## Depends on

- [The FRI protocol](fri-protocol.md)

## Sources

- Eli Ben-Sasson, Iddo Bentov, Yinon Horesh and Michael Riabzev, "Fast Reed–Solomon Interactive Oracle Proofs of Proximity", 45th International Colloquium on Automata, Languages, and Programming (ICALP 2018), 2018.
