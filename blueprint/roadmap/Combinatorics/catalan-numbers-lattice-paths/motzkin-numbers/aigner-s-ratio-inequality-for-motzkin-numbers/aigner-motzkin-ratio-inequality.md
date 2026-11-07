# Aigner's ratio inequality for Motzkin numbers, explicit sum form

For $r \ge 0$ let
$M_r = \sum_{k=0}^{\lfloor r/2 \rfloor} \frac{1}{k+1}\binom{2k}{k}\binom{r}{2k}$, where each
factor $\frac{1}{k+1}\binom{2k}{k}$ is the $k$-th Catalan number, an integer. Then for every
$n \ge 1$, in the rational numbers,

$$
\frac{M_n - M_{n-1}}{M_{n+1} - M_n} \le \frac{M_n}{M_{n+1}}.
$$

## Sources

- Takashi Agoh and Horst Alzer, "Mean Value Inequalities for Motzkin Numbers", Journal of Integer Sequences 24 (2021), Article 21.6.8: Motzkin-number definition, lines 89--107, span SHA-256 `25821864e9da743abcc457fc8eb6b4552118fe71e96860b9dcfccafd67265509`; Aigner ratio inequality, lines 373--386, equation (11), span SHA-256 `c1aac7efaa47a655d6ec5700396a2da6d327480cb691be23c5438f68f4c54292`; source file SHA-256 `b4e1a1ea2e4c22d7d5ee39e09ccac420b7f09db9eeacc83d0023e1deacb051d6`. Stable identifiers: queue item `jis_grounded_4ec4cac48d863b8ffa953aa1`, record `jis_grounded_4ec4cac48d863b8ffa953aa1__aigner_motzkin_ratio_inequality`, named dependency/concept `jis_dep_ed005189a28461a49aaf0092`. The same inequality for the canonical `MetaMathlibExt.motzkinNumber` is `motzkinNumber_ratio_inequality`.
- <https://cs.uwaterloo.ca/journals/JIS/VOL24/Alzer/alzer8.tex>.
