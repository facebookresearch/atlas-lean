# Limits on list recovery of folded Reed-Solomon codes

Let $s \ge 1$, $2 \le \ell \le L$, $q \ge \ell$, let $\gamma$ generate $\mathbb{F}_q^{\times}$ and $m = \lceil \log_\ell(L+1) \rceil \ge 2$. Consider an $s$-folded Reed-Solomon code of length $n$, degree bound $k$ and rate $R = k/(sn)$ with appropriate evaluation points (the $sn$ elements $\gamma^{i}\alpha_j$ are distinct), and assume $R \le (m-1)/m$ and $(k-1)/s \ge m$. If the code is $(\rho, \ell, L)$-list recoverable, then

$$
\rho \le \frac{L + 1 - \ell}{L + 1}\Big(1 - \frac{mR}{m - 1}\Big) + \frac{5}{n} .
$$

Thus the code is not list recoverable at any radius above this bound. For $(\ell, L) = (2, 3)$, where $m = 2$ and the bound is $\frac12 - R + \frac5n$, the matching positive result holds: if $q > n$ and $s \ge 3$, the code is $\big(\frac12 - \frac{sR}{s-2}, 2, 3\big)$-list recoverable, so the bound is tight up to the factor $s/(s-2)$ and the $5/n$ term.

## Proof sketch

Let $p = \lfloor \frac{m}{m-1} \lfloor \frac{k-1}{s} \rfloor \rfloor$, let $Q_i$ be the vanishing polynomial of the $i$-th folded block, and arrange $Q_1, \dots, Q_p$ into $m$ products $f_t = M / M_t$, where each $Q_u$ is omitted from exactly one $f_t$; then $\deg f_t \le k - 1$ and $f_1, \dots, f_m$ are linearly independent. Fix distinct $\beta_1, \dots, \beta_\ell \in \mathbb{F}_q$; the $\ell^m \ge L + 1$ polynomials $\sum_t \beta_{j_t} f_t$ are distinct, and on each of the first $p$ blocks every one of them agrees with one of $\ell$ multiples $\beta_j C(f_t)$, which form the input list there. Choose $L + 1$ of these polynomials $g_1, \dots, g_{L+1}$; on each remaining block the input list consists of the values of $\ell$ of the $g_v$, chosen so that each $g_v$ appears in at least $\lfloor \ell(n-p)/(L+1) \rfloor$ of these lists. All $L + 1$ selected codewords are then within distance $\lceil (L+1-\ell)(n-p)/(L+1) \rceil$ of the input lists, which gives the bound. The $(2, 3)$ positive result extends the agreement-hypergraph argument for list decoding to table-agreement hypergraphs.

## Depends on

- [List recovery and relaxed generalized Singleton bounds](list-recovery-of-folded-codes.md)
- [Folded Reed-Solomon codes](folded-reed-solomon-codes.md)

## Proof depends on

- [Chen-Zhang: explicit FRS and multiplicity codes achieve relaxed generalized Singleton bounds](folded-reed-solomon-codes-achieve-relaxed-generalized-singleton-bounds.md)

## Sources

- Yeyuan Chen, Zihan Zhang, "Explicit folded Reed-Solomon and multiplicity codes achieve relaxed generalized Singleton bounds", STOC (2025); arXiv:2408.15925, Theorems 1.7, 1.8 and 3.1 and Corollary 3.2.
