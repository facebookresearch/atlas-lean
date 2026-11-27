# Multi-resolution knockoff e-values

Let $Y$ be a phenotype and $X_1, \dots, X_p$ genotypes. For a set $\mathcal M$ of resolutions, let $\mathcal A_m$ be a partition of $\{1,\dots,p\}$ into groups and test the conditional independence hypotheses $H_A: Y \perp X_A \mid X_{-A}$ for $A \in \mathcal A_m$; set $\mathcal A = \bigcup_m \mathcal A_m$. For each $m$, construct group knockoffs $\tilde X^m$ (pairwise exchangeable with $X$ on every group of $\mathcal A_m$ and independent of $Y$ given $X$) and antisymmetric knockoff scores $W_A$.

**KeLP e-values.** Choose $c_m \ge 0$ with $\sum_m c_m \le |\mathcal A|$ and $\gamma_m \in (0,1)$. Let

$$T_m = \inf\left\{t > 0 : \frac{1 + \sum_{A\in\mathcal A_m}\mathbf 1\{W_A \le -t\}}{\sum_{A\in\mathcal A_m}\mathbf 1\{W_A \ge t\}} \le \gamma_m\right\}, \qquad e_A = c_m\,\frac{\mathbf 1\{W_A \ge T_m\}}{1 + \sum_{B\in\mathcal A_m}\mathbf 1\{W_B \le -T_m\}}$$

for $A \in \mathcal A_m$ (Gablenz and Sabatti 2025, Procedure 2, Eqs. 12–13). Then $\sum_{A:\,H_A\text{ null}} \mathbb{E}[e_A] \le \sum_m c_m \le |\mathcal A|$ (Eq. 14), so these are relaxed e-values; feeding them into the self-consistent e-value linear program yields disjoint discoveries at the finest resolution the signal supports, with FDR control across all resolutions. With one resolution, KeLP coincides with the ordinary knockoff filter.

## Depends on

- [Self-consistent e-value linear program for non-redundant discoveries](self-consistent-e-value-linear-program-for-non-redundant-discoveries.md)
- [Knockoff threshold](../../../../Probability/hypothesis-testing/knockoff-filter/knockoff-threshold.md)

## Expansion

At each resolution the knockoff stopping time is a stopping time for the sign-flip filtration of null scores, and the optional-stopping argument behind the knockoff filter gives $\sum_{A \in \mathcal A_m\text{ null}}\mathbb{E}[\mathbf 1\{W_A \ge T_m\}/(1 + \#\{W_B \le -T_m\})] \le 1$. Scaling by $c_m$ and summing over resolutions gives the relaxed e-value budget, regardless of the dependence between knockoff runs at different resolutions. In GWAS fine-mapping, coarse groups (large LD blocks) are rejected only when finer groups lack enough evidence.

## Sources

- P. Gablenz and C. Sabatti, *Catch me if you can: signal localization with knockoff e-values*, Journal of the Royal Statistical Society Series B 87(1) (2025), 56–73, Procedure 2 and Eqs. (12)–(14). <https://doi.org/10.1093/jrsssb/qkae042> (PMCID: PMC11809227)
