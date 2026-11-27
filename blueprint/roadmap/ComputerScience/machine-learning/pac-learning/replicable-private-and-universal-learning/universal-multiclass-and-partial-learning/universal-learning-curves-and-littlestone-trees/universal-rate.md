# Realizable distributions, learning curves and universal rates

Let $X$ be a Polish space and $H \subseteq \{0,1\}^X$ a concept class that is measurable in the sense of the source (there are a Polish space $\Theta$ and a Borel map $h : \Theta \times X \to \{0,1\}$ with $H = \{h(\theta, \cdot) : \theta \in \Theta\}$). A distribution $P$ on $X \times \{0,1\}$ is **realizable** by $H$ if $\inf_{h \in H} \mathrm{er}_P(h) = 0$, where $\mathrm{er}_P(h) = P\{(x,y) : h(x) \ne y\}$. A learner is a sequence of universally measurable maps $H_n : (X \times \{0,1\})^n \times X \to \{0,1\}$, with output $\hat h_n(x) = H_n((X_1,Y_1), \dots, (X_n,Y_n), x)$ on an i.i.d. sample $(X_i,Y_i) \sim P$; its **learning curve** on $P$ is $n \mapsto \mathbb{E}[\mathrm{er}_P(\hat h_n)]$.

For a rate function $R : \mathbb{N} \to [0,1]$ with $R(n) \to 0$:

- $H$ is **learnable at rate** $R$ if some learner satisfies: for every realizable $P$ there are $C, c > 0$ with $\mathbb{E}[\mathrm{er}_P(\hat h_n)] \le C R(cn)$ for all $n$;
- $H$ is **not learnable faster than** $R$ if for every learner there is a realizable $P$ and $C, c > 0$ with $\mathbb{E}[\mathrm{er}_P(\hat h_n)] \ge C R(cn)$ for infinitely many $n$;
- $R$ is the **optimal universal rate** if both hold;
- $H$ **requires arbitrarily slow rates** if $H$ is not learnable faster than $R$ for every rate function $R$ with $R(n) \to 0$.

The constants may depend on $P$; this is the difference from the distribution-free PAC model, where they must be uniform over $P$. The definition is stated for deterministic learners; the lower bounds of the source also hold for randomized ones.

## Depends on

- [Expected risk](../../../../generalization-bounds-and-concentration/risk.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483, Section 1.4 (Definition 1.4) and Definition 3.3.
