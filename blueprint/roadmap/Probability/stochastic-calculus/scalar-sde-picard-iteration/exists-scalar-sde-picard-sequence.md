# All-time scalar SDE Picard iteration

Let $B$ be a real Brownian motion on $(\Omega,\mathcal A,P)$, adapted to $(\mathcal F_t)$, with $B_t-B_s$ independent of $\mathcal F_s$ for $s\le t$. Suppose every filtration sigma algebra contains all $P$-null sets. Let $\sigma,b:\mathbb R\to\mathbb R$ be globally Lipschitz with a common constant $K\ge0$, and fix $x\in\mathbb R$.

There are sequences of real processes $X^n,J^n$ on all nonnegative times such that $X^0_t=x$ and

$$X^{n+1}_t=x+J^n_t+\int_0^t b(X^n_s)\,ds.$$

For every $n$, $X^n$ is progressive, continuous on every sample path, and has finite integrated second moment on every finite horizon. Each $J^n$ is a progressive martingale with every-path continuity, and for each fixed $t$,

$$J^n_t=\int_0^t\sigma(X^n_s)\,dB_s\quad\text{almost surely}.$$

The update equation using $J^n$ holds for every sample and time. Equality with the selected actual Itô integral is only asserted almost surely at each fixed time. One sequence works for every horizon.

The construction chooses a continuous martingale version for each stochastic update and uses the ordinary time integral for the drift. Lipschitz composition and the integral energy estimates preserve the progressive continuous finite-energy class. This constructs the iterates, without asserting their convergence for general coefficients. Filtration completeness is an explicit sufficient hypothesis, not a necessity claim; right continuity is not required. This is the Picard iteration in Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus* (2016), Theorem 8.3, with the complete-filtration convention of Definition 8.1.
