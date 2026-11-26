# Self-consistent e-value linear program for non-redundant discoveries

Let $\mathcal A$ be a collection of groups $A \subseteq \{1, \dots, p\}$ of individual hypotheses (e.g. variants) at several resolutions, with group null hypotheses $H_A$, weights $w(A) > 0$ (typically decreasing in $|A|$) and nonnegative statistics $e_A$. Write $n = |\mathcal A|$. The statistics are **relaxed e-values** if $\sum_{A: H_A \text{ null}} \mathbb{E}[e_A] \le n$. A rejection set $\mathcal R$ is **self-consistent at level $\alpha$** if every $A \in \mathcal R$ satisfies $e_A \ge n/(\alpha|\mathcal R|)$.

**Theorem.** Any self-consistent e-testing procedure at level $\alpha$ applied to relaxed e-values controls the false discovery rate at level $\alpha$, under arbitrary dependence among the e-values (Gablenz and Sabatti 2025, Theorem 1, generalizing Wang and Ramdas).

**eLP procedure.** With indicators $x_A \in \{0,1\}$, solve

$$\max \sum_{A\in\mathcal A} w(A)\,x_A \quad\text{s.t.}\quad n - \alpha e_A\sum_{B\in\mathcal A} x_B \le n(1 - x_A)\ \ \forall A, \qquad \sum_{A \ni j} x_A \le 1\ \ \forall j$$

(Procedure 1, Eqs. 7a–7d). The first constraint is self-consistency for every rejected group and is vacuous otherwise; the second forces the rejected groups to be disjoint, so only non-redundant discoveries are reported. Hence eLP maximizes the weighted number of disjoint discoveries subject to FDR $\le \alpha$; with a single resolution it reduces to the e-BH procedure.

## Expansion

For a self-consistent $\mathcal R$, $\mathbf 1\{A \in \mathcal R\}/|\mathcal R| \le \alpha e_A/n$ for each $A$, so $\mathrm{FDR} = \mathbb{E}\sum_{A \text{ null}} \mathbf 1\{A\in\mathcal R\}/(|\mathcal R| \vee 1) \le (\alpha/n)\sum_{A\text{ null}}\mathbb{E}[e_A] \le \alpha$. No dependence assumption is used, which is why e-values suit groups at different resolutions built from the same data.

## Sources

- P. Gablenz and C. Sabatti, *Catch me if you can: signal localization with knockoff e-values*, Journal of the Royal Statistical Society Series B 87(1) (2025), 56–73, Eqs. (3)–(7), Procedure 1 and Theorem 1. <https://doi.org/10.1093/jrsssb/qkae042> (PMCID: PMC11809227)
