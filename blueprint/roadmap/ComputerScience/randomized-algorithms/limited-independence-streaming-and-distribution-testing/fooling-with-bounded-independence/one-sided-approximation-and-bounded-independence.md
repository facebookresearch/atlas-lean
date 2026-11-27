# Braverman's one-sided approximation route to fooling by bounded independence

Let $\mu$ be a $k$-wise independent distribution on $\{0,1\}^n$ and $U$ the uniform distribution. (Mollification.) If a real function $f$ agrees with a Boolean function $F$ off an error event $E$, is bounded by $L$ in absolute value, and $\tilde E$ approximates the indicator of $E$ with $\mathbb{E}_U(\tilde E - \mathbf{1}_E)^2 \le \delta$, then $f(1 - \tilde E)$ vanishes wherever $F \vee \mathbf{1}_E$ is false and $\mathbb{E}_U\bigl((F \vee \mathbf{1}_E) - f(1 - \tilde E)\bigr)^2 \le 2\Pr_U[E] + 2L^2\delta$. (Squaring trick.) If a polynomial $g$ vanishes wherever a Boolean function $G$ is false, then $1 - (1 - g)^2 \le G$ pointwise, it has degree at most twice that of $g$, and $\mathbb{E}_U[G - (1 - (1-g)^2)] = \mathbb{E}_U(G - g)^2$. (One-sided chain.) If $\mu$ and $U$ both see $F \ne F'$ with probability at most $a$, and a polynomial $P$ of degree at most $k$ satisfies $P \le F'$ with $\mathbb{E}_U[F' - P] \le b$, then $\mathbb{E}_\mu F \ge \mathbb{E}_U F - 2a - b$. Combining the three, and applying them to $F$ and to $1 - F$, gives two-sided fooling of any function that is approximated by a low-degree polynomial off a rare witness event whose indicator has a low-degree $L^2$ approximation; this is the analytic core of the proof that polylogarithmic independence fools $\mathrm{AC}^0$.

## Proof sketch

Mollification: $f(1 - \tilde E)$ vanishes wherever $F' \vee E$ is false and is $L^2$-close to it. Squaring trick: if $g$ vanishes where a Boolean $G$ is false, then $1 - (1-g)^2 \le G$ and its expected gap to $G$ equals $\|G - g\|_2^2$. Low degree makes the expectation identical under $\mu$ and $U$.

## Depends on

- [k-wise independent hash families](../../../data-structures/hashing/succinct-dictionaries-and-hash-families/word-ram-hash-families/k-wise-independent-hash-family.md)

## Sources

- M. Braverman, "Polylogarithmic Independence Fools AC0 Circuits", Journal of the ACM, 2010.
