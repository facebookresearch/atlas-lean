# Multicalibration yields the hard-core lemma with optimal density

Let $X$ be a finite domain with a distribution $D$, let $F$ be a family of functions $f : X \to \{0,1\}$, and let $\varepsilon, \delta > 0$. Write $F_{t,q}$ for the functions computed by circuits of size $t$ with $q$ oracle gates from $F$. There are $t = \mathrm{poly}(\log|X|, 1/\varepsilon, 1/\delta)$ and $q = \mathrm{poly}(1/\varepsilon, 1/\delta)$ such that if $g : X \to \{0,1\}$ is $\delta$-hard for $F_{t,q}$ on $D$ (every $f \in F_{t,q}$ has $\Pr_D[f(x) \ne g(x)] \ge \delta$), then there is a distribution $H$ that is $2\delta$-dense in $D$ ($H \le D/(2\delta)$ pointwise) on which $g$ is $(\tfrac12 - \varepsilon)$-hard for $F$. The density $2\delta$ is optimal (Holenstein's bound), since a hardcore distribution of density $\rho$ already makes $g$ about $\rho/2$-hard; the regularity-lemma proof of Trevisan, Tulsiani and Vadhan gives only density $\delta$. The proof through multicalibration gives more: for every $g$, with no hardness assumption, a partition of $X$ of low complexity relative to $F$ whose every large piece $P$ carries a hardcore distribution of density $2b_P$ in $D|_P$, where $b_P = \min(v_P, 1 - v_P)$ and $v_P = \mathbb{E}_{D|_P}[g]$.

## Proof sketch

Take a multicalibrated partition for $g$ with respect to $F$, of complexity polynomial in $1/\varepsilon$ relative to $F$. On each large piece $P$, $g$ is indistinguishable by $F$ from a coin of bias $v_P$, and a characterization of indistinguishability from constant-Bernoulli functions gives a distribution of density $2b_P$ in $D|_P$ on which $g$ is nearly unpredictable. If $\mathbb{E}_P[b_P] < \delta$, guessing the majority value of $g$ on the piece containing $x$, which a circuit in $F_{t,q}$ can do, would err with probability less than $\delta$, contradicting hardness; so $\mathbb{E}_P[b_P] \ge \delta$, and gluing the local hardcore distributions gives a distribution of density at least $2\delta$.

## Depends on

- [Multicalibrated predictors](multicalibrated-predictor.md)

## Proof depends on

- [Multicalibration by iterated level-set corrections terminates quickly](multicalibration-iterative-algorithm.md)

## Sources

- S. Casacuberta, C. Dwork, S. Vadhan, "Complexity-Theoretic Implications of Multicalibration", STOC (2024), arXiv:2312.17223, Theorems 1.4, 3.1 and 3.2, Proposition 3.3.
- L. Trevisan, M. Tulsiani, S. Vadhan, "Regularity, Boosting, and Efficiently Simulating Every High-Entropy Distribution", CCC (2009).
