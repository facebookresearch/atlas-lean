# An OCRS yields a prophet inequality

If a matroid $\mathcal{M}$ has a $c$-selectable OCRS (against the adversary that chooses the order), then $\mathcal{M}$ has a prophet inequality with ratio $c$: there is an online policy with $\mathbb{E}[X(S)] \ge c\,\mathbb{E}[\max_{I \in \mathcal{I}} X(I)]$.

## Proof sketch

Let $I^*$ be the prophet's optimal set and set $x_e = \Pr[e \in I^*]$, so $x \in P_{\mathcal{M}}$. Define thresholds $t_e$ with $\Pr[X_e \ge t_e] = x_e$ (randomizing at atoms) and treat $e$ as active when $X_e \ge t_e$. Running the OCRS selects each $e$ with probability at least $c x_e$, independently of the value of $X_e$ given activity, so $\mathbb{E}[X(S)] \ge c \sum_e x_e\,\mathbb{E}[X_e \mid X_e \ge t_e] \ge c\,\mathbb{E}[X(I^*)]$, the last step because the top $x_e$-quantile of $X_e$ dominates the contribution of $e$ to the prophet.

## Depends on

- [Online contention resolution schemes](online-contention-resolution.md)
- [Matroid prophet inequality](matroid-prophet-problem.md)

## Sources

- Moran Feldman, Ola Svensson, Rico Zenklusen, "Online Contention Resolution Schemes", SODA (2016), arXiv:1508.00142.
- Euiwoong Lee, Sahil Singla, "Optimal Online Contention Resolution Schemes via Ex-Ante Prophet Inequalities", ESA (2018), arXiv:1806.09251.
