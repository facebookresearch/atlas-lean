# Gelman–Rubin potential scale reduction: definition and stationarity limits

Let $m\ge2$ chains each have $n\ge2$ retained draws $x_{ij}$ of a scalar quantity, $i=1,\dots,m$, $j=1,\dots,n$. Write $\bar x_{i\cdot}$ for the chain means, $\bar x_{\cdot\cdot}$ for the grand mean, and

$$W=\frac1m\sum_{i=1}^m s_i^2,\quad s_i^2=\frac1{n-1}\sum_{j=1}^n(x_{ij}-\bar x_{i\cdot})^2,\qquad \frac Bn=\frac1{m-1}\sum_{i=1}^m(\bar x_{i\cdot}-\bar x_{\cdot\cdot})^2,$$

the within-chain variance and the between-chain variance of the means. The pooled variance estimate is $\widehat V=\frac{n-1}nW+\frac Bn$, and for $W>0$ the potential scale reduction is $\widehat R=\sqrt{\widehat V/W}$. (Gelman and Rubin's version adds $B/(mn)$ to $\widehat V$ and multiplies $\widehat V/W$ by a Student-$t$ degrees-of-freedom factor $\mathrm{df}/(\mathrm{df}-2)$; the statements below are for the basic ratio.)

- **Algebraic bound.** If $W>0$, then $\widehat R\ge\sqrt{(n-1)/n}$, since $B\ge0$; identical chains give $B=0$ and equality.
- **Stationarity limit.** If $m$ is fixed and each chain is a strictly stationary ergodic sequence (for instance independent draws) whose common marginal law has finite variance $\sigma^2>0$, then $\widehat R\to1$ in probability as $n\to\infty$: each $s_i^2\to\sigma^2$ and each $\bar x_{i\cdot}$ converges to the common mean.
- **No certificate.** $\widehat R$ close to $1$ does not certify convergence to the target: for a multimodal target, chains that all remain in the neighbourhood of one mode can give $\widehat R\approx1$.

## Proof depends on

- [Strong law of large numbers from the ergodic theorem](../../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md)

## Expansion

A full page must establish:

- the algebraic bound and the identical-chains case;
- the stationarity limit from the ergodic theorem for $\bar x_{i\cdot}$ and $s_i^2$, so that $W\to\sigma^2$ and $B/n\to0$, together with continuity of the square root;
- an explicit multimodal counterexample, for instance a chain whose kernel never leaves one of two components of the target's support, started in that component: $\widehat R\to1$ while the chain does not converge to the target;
- the relation to the source's corrected statistic, which also tends to $1$ under the same hypotheses since the degrees of freedom tend to infinity.

## Sources

- A. Gelman and D. B. Rubin, *Inference from iterative simulation using multiple sequences*, Statistical Science 7 (1992), 457–472, <https://wwwusers.ts.infn.it/~milotti/Didattica/Bayes/pdfs/Gelman&Rubin_1992.pdf>, Section 2.2, equation (3) and the potential scale reduction (definitions), and Section 2.4 (multimodal limitation).
