# Well approximable numbers

For a function $\psi : \mathbb{N} \to \mathbb{R}$, the set
$W(\psi)$ of $\psi$-well approximable numbers consists of the real numbers $x \in [0, 1)$ such
that for infinitely many natural numbers $q$ there is an integer $p$ with
$|x - p/q| < \psi(q)/q$.

The fractions $p/q$ need not be in lowest terms, unlike Mathlib's well approximable sets,
which use points of exact additive order $q$. The value $\psi(0)$ is irrelevant.

## Sources

- Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (1).
