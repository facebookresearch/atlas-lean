# A weighted totient asymptotic when a seed exists

Fix a natural $k\ge1$. Suppose some positive totient value $d$ has $kd<\ell(d)$. Then there are
$c_->0$ and $c_+>0$ such that $c_-\le A(f_k;s)\le c_+$ on $0\le s<1$, and

$$
\frac{N_k(x)}{U(x)A(f_k;\theta(x))}\longrightarrow1\qquad(x\to+\infty).
$$

For all sufficiently large real $x$, the same constants satisfy
$(c_-/c_+)V(x)\le N_k(x)\le V(x)$.

## Depends on

- [Weighted counts](weighted-totient-counts.md)
- [Renewal normalization](totient-counting-normalization.md)
- [Arithmetic approximants](finite-coefficients.md)

## Proof depends on

- [Normalized weighted asymptotic](weighted-normalized-count-asymptotic.md)
- [Unweighted asymptotic equivalent](totient-count-asymptotic.md)

## Expansion

A seed contributes positive weight; turn that contribution into a uniform lower bound before forming the ratio. Compare against the unweighted coefficient with explicit slack so the same constants control the final inequalities in the eventual real range.

## Sources

- [TotientAsymptotic.lean — `weighted_totient_asymptotic`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TotientAsymptotic.lean#L128-L140)
