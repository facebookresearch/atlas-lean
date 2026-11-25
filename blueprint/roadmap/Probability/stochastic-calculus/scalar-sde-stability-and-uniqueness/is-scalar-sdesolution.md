# Scalar solutions of a stochastic differential equation

Fix a measure space $(\Omega,\mathcal A,P)$, a filtration $(\mathcal F_t)_{t\ge0}$, a real process $B$, coefficients $\sigma,b:\mathbb R\to\mathbb R$, and $x\in\mathbb R$. A scalar solution is a real process $X$ on nonnegative times with:

- $X_t$ measurable with respect to $\mathcal F_t$ for every $t$;
- a continuous path for every sample;
- finite integrated second moment $\mathbb E\int_{(0,T]}|X_s|^2\,ds$ for every finite $T$;
- for each fixed $t$, the almost-sure equation

$$X_t=x+\int_0^t\sigma(X_s)\,dB_s+\int_0^t b(X_s)\,ds.$$

The stochastic integral is the actual Itô integral. The ordinary integral uses real time, with the process extended to negative times by its value at zero. No Brownian, Lipschitz, completeness or probability-normalization assumption is part of this predicate; these are hypotheses of the results using it. Fixed-time square integrability, uniqueness and quantitative bounds are not fields of the predicate.
