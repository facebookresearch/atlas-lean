# Affine recurrences by the size of the multiplier

Let $b_{t+1} = a b_t + d$ for $t \ge 0$ with real $a, d, b_0$. If $a = 1$, then $b_t = b_0 + t d$, which converges only when $d = 0$. If $a \ne 1$, let $b^* = d/(1 - a)$ be the unique fixed point; then $b_t - b^* = a^t(b_0 - b^*)$ for every $t$. Outside the convergent case $|a| < 1$: for $|a| > 1$, $|b_t - b^*| \to \infty$ unless $b_0 = b^*$, in which case $b_t = b^*$ for all $t$; and for $a = -1$ the sequence alternates between $b_0$ and $d - b_0$.

Proof. Induction on $t$, using $b^* = ab^* + d$ when $a \ne 1$, and $b_{t+1} = b_t + d$ when $a = 1$; the divergence follows from $|a|^t \to \infty$ for $|a| > 1$.

## Background

- [Affine recurrence convergence](affine-recurrence-tendsto.md): the convergent case $|a| < 1$.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
