# Full-permutation mixing and supporting estimates for the Thorp shuffle

Let $N=2^d$ and use the [physical pair-swap-and-rotate law](physical-thorp-step-and-specht-averages.md), writing $\mu_{d,t}$ for the full permutation law after $t$ elementary steps and $u_d$ for the uniform law. From start $\sigma$ use $\mu_{d,t}(g\sigma^{-1})$. The source asserts the following eight blocks together.

1. At $32800d$ steps the full-deck distance tends to zero uniformly over starting decks ($<\epsilon$ eventually for every $\epsilon>0$).
2. For ordered lists of $k$ distinct labels, compare the images under the rotating-frame permutation (remove the net deterministic rotation on the left) with the uniform injective list. The distance is eventually $<\epsilon$ at $256d$ steps, uniformly over $8k\le7N$, all labels and starts. It is eventually at most $N^{-3/2}$ at $1024d$ steps uniformly over $16k\le15N$. At $2048d$ steps the full distance tends to zero, and equals the identity-start distance for each $d$ and start.
3. There is real $p>0$ with $\sum_\mu D_\mu\operatorname{tr}|Q_{d,\mu}|^{2p}\le1+1/16$ for all $d\ge1$. For every integer sweep count $M\ge p$ and start the distance at $Md$ steps is at most $1/8$.
4. For every real $\eta>0$ and real $\kappa$ there is a natural $r\ge1$ such that for all $d\ge1$, diagrams $\mu$ of size $N$ and diagrams $\alpha,\beta,\gamma$ of combined size $N$, the extended logarithm of $D_\mu\operatorname{Re}\operatorname{tr}((Q_{d,\mu}^*Q_{d,\mu})^r)$ is at most $c_d(\eta)S(\alpha,\beta)+B_d(\kappa,|\gamma|)$. Use the tabloid Specht matrix $Q_{d,\mu}$, and take the extended logarithm after embedding the real moment into the extended nonnegative reals (a zero moment gives $-\infty$). There is **no** occurrence hypothesis relating $\mu$ to $\alpha,\beta,\gamma$.
5. There are even $r\ge2$ and $\eta>0$ such that $D_\mu\operatorname{tr}((Q_{d,\mu}Q_{d,\mu}^*)^r)\le D_\mu^{1-\eta}$ for every $d$ and $\mu$ of size $N$.
6. For one integer $v\ge1$, eventually uniformly over starts, the squared density $L^2(u_d)$ difference $N!\sum_g(\mu_{d,vd}(g\sigma^{-1})-1/N!)^2$ is less than any fixed $\epsilon>0$.
7. For one integer $v\ge1$, eventually uniformly over starts the total-variation difference at $vd$ steps is less than any fixed $\epsilon>0$.
8. The least integer $t$ with identity-start total variation at most $1/4$ is $\Theta(\log(2^d))$ as $d\to\infty$. Start-independence follows from uniform translation invariance; the source's units here are individual pair-swap-and-rotate steps.

The budgets in clause 4 are

$$
\begin{aligned}
S(\alpha,\beta)&=\sum_{x\in\alpha}\log\frac{|\alpha|+|\beta|}{\ell_\alpha(x)}
    +\sum_{x\in\beta}\log\frac{|\alpha|+|\beta|}{\ell_\beta(x)},\\
c_d(a)&=a\left(1-\frac{1}{2\sqrt d}\right),\\
B_d(\kappa,l)&=\begin{cases}0& l=0,\\
    \max\{0,\ c_d(\kappa)l\log N-l\log(N/l)\}& l>0.
    \end{cases}
\end{aligned}
$$

Here $\ell_\alpha(x)$ and $\ell_\beta(x)$ are the lengths of the rows containing their respective cells. The sums over empty diagrams are zero.

**Conventions.** Use the physical and rotating-frame permutation laws, the full and injective-list uniform laws, the regular trace and Specht moments, and the exact discrete mixing-time functional.

## Depends on

- [Tabloid Specht modules and all-copy subgroups on occupied boards](occupied-board-specht-model.md)

- [Physical Thorp pair steps and Specht Fourier averages](physical-thorp-step-and-specht-averages.md)

- [Coordinate-fiber sweeps on the binary cube](binary-sweep-step-law.md)

## Proof depends on

The revealed-path and partial-information bounds, representation moment savings, full-deck Fourier summability, and the support-size obstruction supplying the lower order of the mixing time.

## Expansion

Decompose the eight claims and the three information subclauses. Keep all named step constants separate, show rotating-frame and physical laws agree when removing a full number of rotations, track uniformity in list sizes and starts, and prove the conversion from regular moments to full density and then total variation. The $\Theta$ conclusion alone does not carry the quantitative supporting statements.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ThorpRemaining.lean#L543-L546)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/238.md)
- [Accompanying manuscript: Optimal-order mixing of the Thorp shuffle](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Optimal-order-mixing-of-the-Thorp-shuffle-September-26-2026/paper.pdf)
- [Pinned model and normalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ThorpRemaining.lean#L11-L476)
