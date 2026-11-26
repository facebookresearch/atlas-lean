# Identifiability of multivariable Mendelian randomization under a plurality rule

Consider $L$ exposures and an outcome, and $m$ independent genetic instruments. For instrument $i$ let
$b_{X i} = (b_{X_1 i}, \dots, b_{X_L i})^\top \in \mathbb{R}^L$, $b_{X i} \ne 0$, be its true marginal
associations with the exposures and $b_{Y i} \in \mathbb{R}$ its true marginal association with the outcome.
The multivariable summary-data model is

$$b_{Y i} = r_i + \theta_1 b_{X_1 i} + \dots + \theta_L b_{X_L i}, \qquad i = 1, \dots, m,$$

where $\theta = (\theta_1, \dots, \theta_L)^\top$ are the direct causal effects and $r_i$ is the pleiotropic
effect of instrument $i$ (instrument $i$ is *valid* iff $r_i = 0$). Let the ground truth be $(\theta^*, r^*)$,
with valid set $V^* = \{ i : r_i^* = 0 \}$ and $m_0 = |V^*|$. A solution is admissible if it is obtained from a
largest set of instruments with $r_i = 0$.

**Assumption (multivariable plurality).** The matrix $B_{V^*} = [b_{X i}^\top]_{i \in V^*} \in \mathbb{R}^{m_0 \times L}$
has full column rank $L$ (so $m_0 \ge L$), and

$$|V^*| > \max_{c \in \mathbb{R}^L,\ c \ne 0} \bigl|\{ i : r_i^* = b_{X i}^\top c \}\bigr| .$$

**Theorem.** Given $\{(b_{Y i}, b_{X i})\}_{i=1}^m$, the parameters $(\theta^*, r^*)$ are identifiable (the admissible
solution is unique) if and only if the multivariable plurality assumption holds.

For $L = 1$ the condition reduces to the univariable plurality rule
$|V^*| > \max_{c \ne 0} |\{ i : r_i^*/b_{X_1 i} = c \}|$: no group of invalid instruments sharing a common
ratio $b_{Yi}/b_{X_1 i}$ is as large as the valid group.

## Depends on

- [Linear moment model for instrumental variables](linear-moment-model.md)
- [Ratio estimate of a single SNP](ratio-estimate.md)

## Expansion

Any $c \in \mathbb{R}^L$ yields an alternative solution $\theta = \theta^* + c$, $r_i = r_i^* - b_{X i}^\top c$, whose
zero set is $\{ i : r_i^* = b_{X i}^\top c \}$. Admissible solutions maximize the size of the zero set; the true
solution has zero set $V^*$, so it is the unique maximizer iff every alternative zero set is strictly smaller,
and full column rank of $B_{V^*}$ makes $\theta$ unique once the zero set is fixed. (Lin, Xue and Pan 2023,
Assumption 1, Equation 3 and Theorem 1; proof in their supplement, Section S1.1.)

## Sources

- Zhaotong Lin, Haoran Xue, Wei Pan, "Robust multivariable Mendelian randomization based on constrained maximum likelihood", The American Journal of Human Genetics (2023), <https://doi.org/10.1016/j.ajhg.2023.02.014> (PMC10119150).
