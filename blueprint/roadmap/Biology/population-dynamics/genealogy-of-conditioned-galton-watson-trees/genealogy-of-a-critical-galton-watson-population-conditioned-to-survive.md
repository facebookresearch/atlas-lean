# Genealogy of a critical Galton–Watson population conditioned to survive

**Setting.** Let $(Z_n)_{n \ge 0}$ be a Galton–Watson process with $Z_0 = 1$, offspring law $(p_k)$ of mean $1$ (critical) and finite variance $\sigma^2 > 0$. Condition on survival to generation $n$, $\{Z_n > 0\}$, and look at an intermediate generation $\lfloor nt \rfloor$, $0 < t < 1$. Following Geiger's spine construction, the conditioned tree has a distinguished line of descent to generation $n$; at generation $\lfloor nt\rfloor$ the population splits into $\tilde Z^l_{nt}$ individuals descending from siblings of the spine to its **left** (whose subtrees are conditioned to die out before $n$) and $\tilde Z^r_{nt}$ to its **right** (unconditioned), the spine individual counted in both, so $Z_{nt} = \tilde Z^l_{nt} + \tilde Z^r_{nt} - 1$.

**Theorem.** As $n \to \infty$, for fixed $0 < t < 1$ and $x \ge 0$:
1. $\mathbb{P}(\tilde Z^r_{nt}/n \ge x) \to \exp\!\big(-\tfrac{2x}{t\sigma^2}\big)$ and $\mathbb{P}(\tilde Z^l_{nt}/n \ge x) \to \exp\!\big(-\tfrac{2x}{t(1-t)\sigma^2}\big)$, and the two parts are asymptotically independent.
2. *(Spitzer–Lamperti–Ney limit.)* Conditionally on $Z_n > 0$,
$$\frac{Z_{\lfloor nt \rfloor}}{n} \Rightarrow U_t + V_t,$$
with $U_t, V_t$ independent exponentials of rates $2/(t(1-t)\sigma^2)$ and $2/(t\sigma^2)$.
3. *(Most recent common ancestor.)* Let $G_{nt}$ be the generation of the most recent common ancestor of all individuals at generation $\lfloor nt\rfloor$. For $0 \le x \le t$,
$$\lim_{n\to\infty}\mathbb{P}\Big(\frac{G_{nt}}{n} \le x \,\Big|\, Z_n > 0\Big) = 1 - \frac{(t-x)^2}{t^2(1-x)}.$$
4. *(Successive branch points.)* Rescaled by $nt$, the depths of the successive branch points of the right subtree along the spine converge to nested uniforms $U_1 > U_2 > \cdots$ ($U_k$ uniform on $[0, U_{k-1}]$), and each branch point carries asymptotically exactly one surviving side lineage; for the left subtree the same holds after the change of variable $g_t(x) = x/(tx + 1 - t)$.

At $t = 1$ the right part is the whole population and part 1 is Yaglom's exponential limit with mean $\sigma^2/2$.

## Expansion

Conditioning on survival to time $n$ makes the population at time $nt$ the union of side bushes grafted onto the spine. Each right bush is an unconditioned critical tree, so only those grafted at depth comparable to $n$ reach generation $nt$ with many members; in the limit their grafting times form a nested-uniform (Poisson-like, log-scale) sequence and each contributes an exponential mass, summing to an exponential. Left bushes must die before $n$, which by a Doob transform turns them into a branching process in a varying environment whose survival is penalized by the factor $1-t$, shrinking the mean to $t(1-t)\sigma^2/2$. The MRCA law follows from the joint law of the first left and right branch points, which are asymptotically independent.

## Sources

- Jiayan Guo and Wenming Hong, "The Genealogy of Conditioned Critical Galton–Watson Trees", arXiv:2510.23308 (2025), Theorems 1.2, 1.5, 1.7, 1.9, 1.11, 1.14 and 1.15, Corollary 1.13, <https://doi.org/10.48550/arXiv.2510.23308>.
