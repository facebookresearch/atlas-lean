# Direction of gene-drive travelling waves for small fitness cost

In the [gene drive model](gene-drive-reaction-diffusion-model.md), let $(p, n)(t, x) = (P, N)(x - ct)$ be a nontrivial travelling wave with $(P, N)(-\infty) = (0, 1)$, $P$ strictly monotonic and $P$ converging exponentially fast to $0$ at $-\infty$. Wild-type individuals occupy the left and the drive the right, so $c < 0$ means the drive invades the wild-type region.

**Theorem.** If $s \le 1/2$, then $c < 0$, $P(+\infty) = 1$, and

$$c \le -2\sqrt{1 - 2s}.$$

 The paper gives further parameter regions with $1/2 < s < 2/3$ where $c < 0$, and regions with $s \ge 1/2$ where $c > 0$ (the drive retreats).

## Depends on

- [Reaction–diffusion model of a gene drive with demographic feedback](gene-drive-reaction-diffusion-model.md)

## Proof depends on

- [Reaction–diffusion model of a gene drive with demographic feedback](gene-drive-reaction-diffusion-model.md)
- [Every Fisher–KPP front speed is at least the minimal speed](../../pattern-formation/fisher-kpp-travelling-waves/two-mul-sqrt-le-of-is-front.md)

## Expansion

For $s \le 1/2$ the frequency threshold $(2s-1)/s$ is nonpositive, so the drive is favoured at every frequency; at the leading edge, where $n_D$ is small and $n \approx 1$, linearizing the $n_D$ equation gives growth rate $2(1-s) - 1 = 1 - 2s$ and diffusion $1$, which yields the Fisher–KPP-type bound $|c| \ge 2\sqrt{1 - 2s}$ for a wave moving into the wild-type region. The sign of $c$ in the other regimes is determined through a formula of Nadin, Strugarek and Vauchelet expressing $\operatorname{sign}(c)$ as the sign of an integral along the wave profile.

## Sources

- L. Girardin and F. Débarre, *Demographic feedbacks can hamper the spatial spread of a gene drive*, J. Math. Biol. 83 (2021). <https://doi.org/10.1007/s00285-021-01702-2> Theorem 1.2 and Propositions 2.3–2.6.
