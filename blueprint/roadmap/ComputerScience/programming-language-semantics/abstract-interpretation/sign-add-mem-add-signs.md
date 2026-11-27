# Soundness of abstract sign addition

Write $\operatorname{sgn} : \mathbb{Z} \to \{-, 0, +\}$ for the sign of an integer ($-$ for negative, $0$ for zero, $+$ for positive). Abstract addition $\oplus$ on signs is given by $0 \oplus t = \{t\}$, $s \oplus 0 = \{s\}$, $s \oplus s = \{s\}$ for $s \ne 0$, and $(-) \oplus (+) = (+) \oplus (-) = \{-, 0, +\}$. For all integers $a$ and $b$,

$$\operatorname{sgn}(a + b) \in \operatorname{sgn}(a) \oplus \operatorname{sgn}(b).$$
