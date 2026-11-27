# Realizable distributions, learning curves and universal rates

Let $H \subseteq \{0,1\}^X$ be a concept class on a measurable domain. A distribution $P$ on $X \times \{0,1\}$ is **realizable** by $H$ if $\inf_{h \in H} \mathrm{er}_P(h) = 0$, where $\mathrm{er}_P(h) = P\{(x,y) : h(x) \ne y\}$. A learner is a sequence of measurable maps $\hat h_n : (X \times \{0,1\})^n \to \{0,1\}^X$; its **learning curve** on $P$ is $n \mapsto \mathbb{E}[\mathrm{er}_P(\hat h_n(S_n))]$ with $S_n \sim P^n$.

For a rate function $R : \mathbb{N} \to [0,1]$ with $R(n) \to 0$:

- $H$ is **learnable at rate** $R$ if some learner satisfies: for every realizable $P$ there are $C, c > 0$ with $\mathbb{E}[\mathrm{er}_P(\hat h_n)] \le C R(cn)$ for all $n$;
- $H$ is **not learnable faster than** $R$ if for every learner there is a realizable $P$ and $C, c > 0$ with $\mathbb{E}[\mathrm{er}_P(\hat h_n)] \ge C R(cn)$ for infinitely many $n$;
- $R$ is the **optimal universal rate** if both hold;
- $H$ **requires arbitrarily slow rates** if for every $R \to 0$ and every learner there is a realizable $P$ with $\mathbb{E}[\mathrm{er}_P(\hat h_n)] \ge R(n)$ for infinitely many $n$.

The constants may depend on $P$; this is the difference from the distribution-free PAC model, where they must be uniform over $P$.

## Depends on

- [Expected risk](../../../../generalization-bounds-and-concentration/risk.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483.
