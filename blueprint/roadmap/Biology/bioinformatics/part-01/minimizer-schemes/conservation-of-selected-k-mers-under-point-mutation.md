# Conservation of selected k-mers under point mutation

**Mutation model.** Let $S = x_1 x_2 \cdots$ be a uniformly random i.i.d. string and $S' = x'_1 x'_2 \cdots$ a mutated copy with $\Pr(x'_i = x_i) = 1 - \theta$ independently, a mutated base being uniform on the other letters ($\theta \in [0,1]$).

**Spread.** For a local selection method $f$ (see [local k-mer selection methods](local-k-mer-selection-methods-and-their-densities.md)) and a position $i$ away from the ends, let $E_j$ be the event that the $k$-mer starting at $j$ is selected, and

$$\Pr(f, \alpha) = \Pr\Big(\bigcup_{j=i}^{i+\alpha-1} E_j\Big), \qquad \Pr(f) = \big[\Pr(f,1), \dots, \Pr(f,k)\big].$$

$\Pr(f, 1)$ is the density $d$, and the union bound gives $\Pr(f, \alpha) \le \min(1, \alpha d)$; large values mean selected $k$-mers are spread out rather than clumped.

**Conservation.** Base $i$ is *conserved* if some $k$-mer covering it is selected in both $S$ and $S'$ at the same position; $\mathrm{Cons}(f, \theta, k)$ is the expected fraction of conserved bases. Let $\alpha(\theta, k)$ be the number of $k$-mers covering a fixed base that are unmutated, and $\Pr(\alpha(\theta,k)) = [\Pr(\alpha = 1), \dots, \Pr(\alpha = k)]$.

**Theorem (conservation = spread · runs).** If $f$ is $1$-local,

$$\mathrm{Cons}(f, \theta, k) = \Pr(f) \cdot \Pr(\alpha(\theta, k)),$$

and for any local $f$ the right-hand side is an upper bound (selection of a shared $k$-mer can be destroyed by mutations elsewhere in its window, the context dependency of minimizers).

**Run probabilities.** The $k$-mers covering a base span $2k - 1$ positions, and $\alpha = \beta + 1$ iff the longest run of unmutated bases among them has length $k + \beta$. For $0 \le \beta < k - 1$,

$$\Pr\big(\alpha(\theta, k) = \beta + 1\big) = \big(2 + \theta(k - \beta - 2)\big)\,(1-\theta)^{k+\beta}\,\theta,$$

and $\Pr(\alpha(\theta,k) = k) = (1-\theta)^{2k-1}$.

**Syncmer spread.** Assume that the $k - s + \alpha$ $s$-mers in the positions spanned by $\alpha$ consecutive $k$-mers are pairwise distinct, so that their ranks form a uniformly random permutation; for the i.i.d. string this fails with probability at most $(k-s+\alpha)^2/|\Sigma|^s$. Under this assumption, for closed syncmers $(k, s)$, $\Pr(f, \alpha) = \dfrac{2\alpha}{k - s + \alpha}$ for $\alpha \le k - s$ and $\Pr(f, \alpha) = 1$ for $\alpha > k - s$. For open syncmers $(k, s, t)$, $\Pr(f, \alpha) = OS(\alpha, k, s, t)/(k-s+\alpha)!$, where the count $OS$ of permutations of $k - s + \alpha$ ranks having some window of $k - s + 1$ consecutive ranks with its minimum at offset $t - 1$ satisfies a linear recurrence, and the choice $\hat t = \lceil (k-s+1)/2 \rceil$ maximizes $OS(\alpha, k, s, t)$ for every $\alpha$. Hence, with the spreads computed under this distinctness assumption, the middle position maximizes conservation among open syncmers of given $(k, s)$. Without it the formulas are only approximate: at $\alpha = 1$, $k = 3$, $s = 1$ over a binary alphabet the closed-syncmer density is $6/8$ (leftmost minimum) or $7/8$, not $2/3$.

## Depends on

- [Local k-mer selection methods and their densities](local-k-mer-selection-methods-and-their-densities.md)

## Expansion

A base is conserved iff, among its covering $k$-mers, some unmutated one is selected; for a $1$-local method selection of an unmutated $k$-mer is the same in $S$ and $S'$. Unmutated covering $k$-mers form a consecutive block, of length $\alpha$, and conditional on $\alpha$ the selection events depend only on the (unchanged) bases of that block, so the conditional conservation probability is $\Pr(f, \alpha)$; averaging over $\alpha$ gives the dot product. A run of at least $k$ successes among $2k-1$ trials must contain the middle position, which is why "longest run" determines $\alpha$; a run of exactly $m = k + \beta$ is either flush with an end (two placements, one bounding failure) or interior ($k - \beta - 2$ placements, two bounding failures). Under the random-order assumption, the $s$-mer ranks in $k - s + \alpha$ consecutive positions form a uniform random permutation, so $\Pr(f, \alpha)$ is a permutation count divided by $(k - s + \alpha)!$; for closed syncmers $\Pr(f, \alpha)$ reaches the union bound $\min(1, \alpha d)$ only at $\alpha = 1$, while centred open syncmers spread selections more evenly at the same density.

## Sources

- J. Shaw, Y. W. Yu, "Theory of local k-mer selection with applications to long-read alignment", Bioinformatics 38 (2022) 4659–4669, Section 3 (Definitions 8–9, Theorems 3–4, Theorems 6–8, Corollary 1), <https://doi.org/10.1093/bioinformatics/btab790>.
