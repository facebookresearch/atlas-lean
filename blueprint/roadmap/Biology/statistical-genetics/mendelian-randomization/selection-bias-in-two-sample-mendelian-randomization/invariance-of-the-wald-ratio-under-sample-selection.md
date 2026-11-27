# Invariance of the Wald ratio under sample selection

**Setting.** Two-sample Mendelian randomization estimates the causal effect of an exposure $X$ on an outcome $Y$ from genetic instruments $G_1,\dots,G_J$. SNP-exposure associations $\beta_{G_jX}$ are estimated in a sample from population I and SNP-outcome associations $\beta_{G_jY}$ in a sample from population II. Each $G_j$ is a valid instrument: it is associated with $X$, independent of the unmeasured confounders $U$ of $X$ and $Y$, and affects $Y$ only through $X$. Let $S_1,S_2\in\{0,1\}$ indicate selection into samples I and II, so that the analysis conditions on $S_1=1$ and $S_2=1$ and estimates the Wald ratio

$$\frac{\beta_{G_jY\mid S_2=1}}{\beta_{G_jX\mid S_1=1}}\quad\text{in place of}\quad\frac{\beta_{G_jY}}{\beta_{G_jX}}.$$

**Theorem 1 (sufficient conditions for invariance).** For linear (identity-link) association models, the selected-sample Wald ratio equals the population causal ratio,

$$\frac{\beta_{G_jY\mid S_2=1}}{\beta_{G_jX\mid S_1=1}}=\frac{\beta_{G_jY}}{\beta_{G_jX}},$$

if, for every valid instrument $G_j$, either

- (a) $S_1\perp G_j$ or $S_1\perp X\mid G_j$ in population I, and $S_2\perp G_j$ or $S_2\perp Y\mid G_j$ in population II; or
- (b) $G_j\perp Y\mid S_2$ and $G_j\perp Y$ in population II.

**Theorem 2 (binary exposure and outcome, odds ratios).** When $X$ and $Y$ are binary and associations are log odds ratios, the same conclusion holds with the conditions $S_1\perp G_j$ and $S_2\perp G_j$ in (a) replaced by $S_1\perp G_j\mid X$ and $S_2\perp G_j\mid Y$, which non-collapsibility of the odds ratio requires; in particular selection depending only on the outcome in sample II (case-control sampling) leaves the ratio unchanged.

## Depends on

- [Ratio estimate of a single SNP](../ratio-estimate.md)

## Expansion

Selection acts by conditioning on a collider or a descendant in the causal graph $G_j\to X\to Y$, $U\to X$, $U\to Y$. If selection is independent of $G_j$, the instrument's distribution in the selected sample is unchanged and its association with the downstream variable is preserved; if selection depends on the downstream variable only through $G_j$, conditioning on $S$ is conditioning on a function of $G_j$ and again leaves the slope intact. Condition (b) covers the null case: if $G_j$ is independent of $Y$ with and without selection, both numerators vanish. Selection that depends jointly on $X$ and $Y$, or on $G$ and $Y$, in sample II opens a collider path and generally biases the ratio, which matches the simulation finding that such mechanisms in the outcome sample cause the largest biases.

## Sources

- Yu Y, Hou L, Shi X, Sun X, Liu X, Yu Y, Yuan Z, Li H, Xue F, "Impact of nonrandom selection mechanisms on the causal effect estimation for two-sample Mendelian randomization methods", PLoS Genet 2022 Mar 17;18(3):e1010107, Section 2.2, Theorems 1 and 2, <https://doi.org/10.1371/journal.pgen.1010107>, PMCID PMC8963545.
