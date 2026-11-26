# Nonexistence of nontrivial gene-drive travelling waves

In the [gene drive model](gene-drive-reaction-diffusion-model.md) in $(p, n)$ form, a travelling wave is a bounded nonnegative classical solution $(p, n)(t, x) = (P, N)(x - ct)$ with $P$ nondecreasing, $N$ decreasing and $(P, N)(-\infty) = (0, 1)$; it is trivial if $P \equiv 0$.

**Theorem.** If $s > 1/2$ and

$$0 < r \le \frac{2s - 1}{2(1 - s)},$$

then every travelling wave is trivial; consequently $n(t, x) = N(x - ct)$ is a Fisher–KPP travelling wave with speed $c \ge 2\sqrt{r}$. Moreover, for such $r$, any solution of the $(n_D, n_O)$ system with $n_O(0, \cdot) > 0$ has $n_D \to 0$ uniformly in space.

## Depends on

- [Reaction–diffusion model of a gene drive with demographic feedback](gene-drive-reaction-diffusion-model.md)
- [Traveling front of the Fisher–KPP equation](../../../Analysis/ordinary-differential-equations/is-front.md)

## Proof depends on

- [Reaction–diffusion model of a gene drive with demographic feedback](gene-drive-reaction-diffusion-model.md)
- [Every Fisher–KPP front speed is at least the minimal speed](../../pattern-formation/fisher-kpp-travelling-waves/two-mul-sqrt-le-of-is-front.md)

## Expansion

Using $1 + n_O/(n_D + n_O) \le 2$ and $1 - n_D - n_O \le 1 - n_D$, $n_D$ is a subsolution of the logistic equation $\partial_t \bar n - \partial_{xx} \bar n = \bar n\,(-1 + 2(1-s)(r+1) - 2(1-s) r \bar n)$. Its growth rate $-1 + 2(1-s)(r+1)$ is nonpositive exactly when $r \le (2s-1)/(2(1-s))$, so by comparison $n_D$ dies out uniformly. With $P \equiv 0$ the $n$ equation is the Fisher–KPP equation $n_t - n_{xx} = r n(1 - n)$, whose monotone waves have speeds $c \ge 2\sqrt{r}$.

## Sources

- L. Girardin and F. Débarre, *Demographic feedbacks can hamper the spatial spread of a gene drive*, J. Math. Biol. 83 (2021). <https://doi.org/10.1007/s00285-021-01702-2> Definition 1.1, Theorem 1.1, Proposition 2.1 and Corollary 2.2.
