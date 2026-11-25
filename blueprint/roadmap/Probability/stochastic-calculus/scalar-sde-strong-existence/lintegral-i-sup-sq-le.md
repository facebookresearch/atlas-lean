# Maximal second-moment bound for scalar Lipschitz SDE solutions

Let $B$ have real Brownian finite-dimensional laws, be adapted to a filtration $(\mathcal F_t)$, and have each increment $B_t-B_s$ independent of $\mathcal F_s$ for $s\le t$. Let $\sigma,b:\mathbb R\to\mathbb R$ be globally Lipschitz with a common constant $K\ge0$, and fix $x\in\mathbb R$.

Suppose $Y$ is adapted, continuous on every path, and has finite integrated second moment on each finite horizon. Assume that, for each fixed $t\ge0$, almost surely,

$$Y_t=x+\int_0^t\sigma(Y_s)\,dB_s+\int_0^t b(Y_s)\,ds,$$

where the stochastic term is the actual Itô integral. Then, for every $0\le t\le T$,

$$\mathbb E\sup_{0\le s\le t}|Y_s|^2
\le \left[3x^2+\bigl(24\sigma(0)^2+6T b(0)^2\bigr)T\right]
\exp\bigl((24+6T)K^2t\bigr).$$

The expectation is a nonnegative extended integral; Brownian laws imply probability normalization. The estimate includes zero time and $K=0$. No completeness or right continuity of the filtration, or continuous driving paths, are required.

Subtracting the initial value and ordinary drift from $Y$ gives a progressive continuous martingale which equals the stochastic integral at each fixed time almost surely. Doob's inequality first gives finite supremum moments; Lipschitz growth and integral Gronwall then give the displayed bound. The constants are sufficient and nonoptimal. This is the maximal-moment argument accompanying Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus* (2016), Theorem 8.3.
