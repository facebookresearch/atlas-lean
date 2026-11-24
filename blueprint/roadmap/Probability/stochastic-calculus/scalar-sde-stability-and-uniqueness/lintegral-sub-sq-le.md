# Lower-integral mean-square stability of scalar SDEs

Let $B$ have real Brownian finite-dimensional laws, be adapted to $(\mathcal F_t)$, and have increments $B_t-B_s$ independent of $\mathcal F_s$ for $s\le t$. Let $X,Y$ be scalar solutions driven by this same process and filtration, with deterministic initial values $x,y$, and the same coefficients $\sigma,b$. Suppose both coefficients are globally Lipschitz with a common constant $K\ge0$.

For $0\le t\le T$,

$$\int_\Omega |X_t-Y_t|^2\,dP
 \le 3|x-y|^2\exp\bigl(3K^2(1+T)t\bigr).$$

Here the left side is the nonnegative extended integral. The probability normalization follows from the Brownian finite-dimensional laws. No completeness or right continuity of the filtration, or path continuity of $B$, is required. The solutions themselves have continuous paths and locally finite integrated second moments.

The factor three is nonoptimal. A three-term square bound, Itô difference isometry and ordinary Cauchy–Schwarz give an integral inequality. Tonelli and the finite-energy hypotheses justify its real moment conversion before integral Gronwall is applied. This is the standard Lipschitz uniqueness argument; see Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus* (2016), Theorem 8.3.
