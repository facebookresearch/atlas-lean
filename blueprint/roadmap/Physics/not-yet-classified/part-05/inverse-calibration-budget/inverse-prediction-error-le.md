# Inverse prediction error under bounded parameter errors

Let a calibration line have true intercept $a$ and slope $b$, and let $y = b x + a + e$ be an observation of $x$ with error $e$. Suppose $X, D_a, D_b, E \ge 0$, $D_b < |b|$, $|x| \le X$, $|e| \le E$, and the intercept and slope perturbations satisfy $|d_a| \le D_a$, $|d_b| \le D_b$. Then the inverse prediction with perturbed parameters, $\hat x = (y - (a + d_a))/(b + d_b)$, satisfies

$$|\hat x - x| \le \frac{D_b X + D_a + E}{|b| - D_b}.$$
