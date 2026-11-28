# Chi limit law of the $k$th longest external branch of a Yule history

Let $\ell_k$ be the $k$th largest distinct external branch length (rank of the parent node of a leaf) in a Yule-distributed random history of size $n$, as in [the exact law of the longest external branch](exact-law-of-the-longest-external-branch-of-a-yule-history.md). Fix $k \ge 1$. As $n \to \infty$,

$$\frac{n-\ell_k}{\sqrt{n/2}} \xrightarrow{d} \chi(2k),$$

the $\chi$-distribution with $2k$ degrees of freedom (density $x^{2k-1}e^{-x^2/2}/(2^{k-1}(k-1)!)$ on $x \ge 0$), with convergence of all moments:

$$\mathbb{E}\left[\left(\frac{n-\ell_k}{\sqrt{n/2}}\right)^m\right] \longrightarrow 2^{m/2}\,\frac{\Gamma\!\left(\frac{m}{2}+k\right)}{\Gamma(k)}, \qquad m \ge 1.$$

Consequently $\mathbb{E}(\ell_k) \sim n$, more precisely $(n-\mathbb{E}\ell_k)/\sqrt{n/2} \to \sqrt{2\pi}\,k\binom{2k}{k}/4^k$, and

$$\operatorname{Var}(\ell_k) \sim \left(k - \frac{\pi k^2}{16^k}\binom{2k}{k}^2\right) n.$$

For $k=1$ the limit is the Rayleigh$(1)$ law, with $\operatorname{Var}(\ell_1) \sim (1-\pi/4)\,n$.

## Depends on

- [Exact law of the longest external branch of a Yule history](exact-law-of-the-longest-external-branch-of-a-yule-history.md)

## Proof sketch

From the exact distribution function one proves a local limit theorem: uniformly for $0 \le x \le n^{1/7}$,

$$\Pr\bigl(\ell_k = \lfloor n - x\sqrt{n/2}\rfloor\bigr) = \frac{x^{2k-1}}{2^{k-1}(k-1)!\,\sqrt{n/2}}\,e^{-x^2/2}\,(1+o(1)) + O\!\left(\frac{e^{-x^2/2}}{n}\right),$$

and the region $x > n^{1/7}$ carries mass $O(n^{k-1}e^{-n^{2/7}/2})$. The case $k=1$ comes from Stirling's formula applied to the factorial expression; general $k$ follows by induction on $k$ through the two-term recurrence for the joint law, each step convolving with a Rayleigh-type kernel that raises the power of $x$ by two. Summing $x^m$ against the local estimate is a Riemann sum for $\int_0^\infty x^{m+2k-1}e^{-x^2/2}\,dx/(2^{k-1}(k-1)!)$, which gives the moments; moment convergence identifies the $\chi(2k)$ limit. So all of the longest external branches sit within $O(\sqrt n)$ layers of the root: in a neutral gene genealogy, the gene copies with the most singleton mutations branch off near the top of the tree.

## Sources

- Filippo Disanto and Michael Fuchs, "Distribution of External Branch Lengths in Yule Histories", *The Electronic Journal of Combinatorics* 30 (2023), P3.23, <https://doi.org/10.37236/11438>. Preprint version: arXiv:2208.04804 (2022), Section 4: Lemma 1, Proposition 2, Corollary 1, Theorem 1, <https://doi.org/10.48550/arXiv.2208.04804>.
