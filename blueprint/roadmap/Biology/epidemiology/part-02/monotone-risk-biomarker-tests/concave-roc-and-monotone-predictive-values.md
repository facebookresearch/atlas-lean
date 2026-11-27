# Concave ROC curves and monotone predictive values

**Setting.** Let $D \in \{0,1\}$ be disease status with prevalence $p = P(D=1) \in (0,1)$, and let $X$ be a biomarker with risk function $R(x) = P(D = 1 \mid X = x)$. A test with cut-off $c$ is positive when $X > c$, with

$$Se(c) = P(X > c \mid D = 1), \qquad Sp(c) = P(X \le c \mid D = 0),$$

$PPV = P(D=1 \mid X > c)$ and $NPV = P(D = 0 \mid X \le c)$. The ROC curve is the curve $c \mapsto (1 - Sp(c), Se(c))$ from $(0,0)$ to $(1,1)$. Assume (1) $X$ has a continuous distribution and (2) $R$ is strictly increasing.

**Theorem.**
1. The ROC curve is concave. Hence $Se - (1 - Sp) \ge 0$ at every cut-off: the test result is non-negatively correlated with disease, $PPV \ge p$ and $NPV \ge 1 - p$, with equality exactly when the result is independent of $D$.
2. As the cut-off varies, sensitivity and specificity move in opposite directions; $PPV$ decreases as $Se$ increases, and $NPV$ decreases as $Sp$ increases. Consequently $PPV$ and $Sp$ move together, as do $NPV$ and $Se$.

## Depends on

- [Positive predictive value of diagnostic parameters](../../sensitivity-specificity-and-predictive-values/ppv.md)

## Expansion

With class-conditional densities $f_1, f_0$, $R(x) = pf_1(x)/(pf_1(x) + (1-p)f_0(x))$, so $R$ is strictly increasing iff the likelihood ratio $f_1/f_0$ is. The ROC slope at cut-off $c$ is $\frac{dSe}{d(1-Sp)} = f_1(c)/f_0(c)$; as $c$ decreases the curve moves right while its slope decreases, which is concavity. By Bayes,

$$PPV = \frac{p\,Se}{p\,Se + (1-p)(1-Sp)}, \qquad NPV = \frac{(1-p)\,Sp}{(1-p)\,Sp + p(1-Se)},$$

which increase in the slopes $Se/(1-Sp)$ of the chord from $(0,0)$ and $Sp/(1-Se)$ (the reciprocal of the chord slope to $(1,1)$). For a concave curve both chord slopes from the point to the endpoints decrease as the point moves from $(0,0)$ toward $(1,1)$, i.e. as $Se$ increases and $Sp$ decreases, giving the monotone relations. Concavity also puts the curve above the diagonal, so $Se/(1-Sp) \ge 1$ and $PPV \ge p$.

## Sources

- H. Wang, B. Wang, X. Zhang, C. Feng, "Relations among sensitivity, specificity and predictive values of medical tests based on biomarkers", General Psychiatry (2021) e100453, Assumptions 1–2, Theorems 1–2 and Table 1, <https://doi.org/10.1136/gpsych-2020-100453>, PMCID PMC7949469.
