# Maximal difference estimate for Lipschitz time integrals

Let $P$ be any measure, let $X,Y$ be real processes with continuous paths for every sample, and let $b:\mathbb R\to\mathbb R$ be globally Lipschitz with constant $K\ge0$. For every $t\ge0$,

$$\int_\Omega\sup_{0\le s\le t}\left|\int_0^s b(X_u)\,du-\int_0^s b(Y_u)\,du\right|^2\,dP
\le tK^2\int_\Omega\int_0^t|X_u-Y_u|^2\,du\,dP.$$

The outer and energy integrals are nonnegative extended integrals. No sample measurability, finite measure, or finite energy hypothesis is imposed. Continuous paths justify the actual ordinary integrals and their subtraction; Cauchy–Schwarz bounds the difference uniformly over the interval, and Lipschitzness bounds its input energy. Zero horizons and infinite right sides are allowed.
