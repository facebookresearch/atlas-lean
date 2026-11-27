# Contraction principle

Let $X$ be a topological space with a $\sigma$-algebra containing the open sets, let $Y$ be a
Hausdorff space with its Borel $\sigma$-algebra, and let $F : X \to Y$ be continuous. If the
measures $(\mu_n)$ on $X$ satisfy the large deviation principle with a **good** rate function
$I$, then the image measures $(F_* \mu_n)$ satisfy the large deviation principle on $Y$ with the
good rate function

$$J(y) = \inf \{ I(x) : F(x) = y \},$$

with $J(y) = \infty$ off the range of $F$.

The bounds transfer because $F^{-1}$ maps closed sets to closed sets and open sets to open sets,
and $\inf_{F^{-1}(C)} I = \inf_C J$. Goodness of $I$ is needed only to make $J$ a rate function:
each fibre $F^{-1}\{y\}$ is closed, so the infimum defining $J(y)$ is attained on a compact
sub-level set of $I$, and $\{J \le a\} = F(\{I \le a\})$ is compact for finite $a$.

A typical use: Cramér's theorem for sample means follows from Sanov's theorem for empirical
measures by contracting along $\beta \mapsto \int x \, d\beta(x)$ (Varadhan's notes, Section 3,
Corollary 1.3, with a truncation argument since this map is not continuous for the weak topology).

## Sources

- S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010, Section 2, Theorem 2.7 (stated for Polish `X` and `Y`).
