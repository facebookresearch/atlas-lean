# Aigner's ratio inequality for Motzkin numbers, explicit sum form

For $r \ge 0$ let
$M_r = \sum_{k=0}^{\lfloor r/2 \rfloor} \frac{1}{k+1}\binom{2k}{k}\binom{r}{2k}$, where each
factor $\frac{1}{k+1}\binom{2k}{k}$ is the $k$-th Catalan number, an integer. Then for every
$n \ge 1$, in the rational numbers,

$$
\frac{M_n - M_{n-1}}{M_{n+1} - M_n} \le \frac{M_n}{M_{n+1}}.
$$

## Sources

- Takashi Agoh and Horst Alzer, "Mean Value Inequalities for Motzkin Numbers", Journal of Integer Sequences 24 (2021), Article 21.6.8: Motzkin-number definition, lines 89--107; Aigner ratio inequality, lines 373--386, equation (11). The same inequality for the canonical `MetaMathlibExt.motzkinNumber` is `motzkinNumber_ratio_inequality`.
- <https://cs.uwaterloo.ca/journals/JIS/VOL24/Alzer/alzer8.tex>.
