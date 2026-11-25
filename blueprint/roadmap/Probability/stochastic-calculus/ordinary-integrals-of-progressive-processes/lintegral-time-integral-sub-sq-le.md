# Difference estimate for ordinary time integrals

For a real process $H$ indexed by nonnegative time, let

$$D(H)_t(\omega)=\int_0^t H_s(\omega)\,ds.$$

For any measure $P$ and real processes $X,Y$ whose paths are continuous for every sample,

$$\int_\Omega|D(X)_t-D(Y)_t|^2\,dP\le t\int_\Omega\int_{(0,t]}|X_s-Y_s|^2\,ds\,dP.$$

Path continuity guarantees the integrability needed to identify the difference of the actual integrals with the integral of $X-Y$. Applying the squared primitive bound then gives the result. Sample measurability is unnecessary because the moment and energy are nonnegative lower integrals. This is the deterministic integral estimate used alongside the Itô difference isometry in Lipschitz SDE arguments.
