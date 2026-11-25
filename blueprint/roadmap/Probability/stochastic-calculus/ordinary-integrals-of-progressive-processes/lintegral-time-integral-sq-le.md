# Second moment of an ordinary time integral

For a real process $H$ indexed by nonnegative time, let

$$D(H)_t(\omega)=\int_0^t H_s(\omega)\,ds.$$

Write $e_T(H)=\int_\Omega\int_{(0,T]}|H_s(\omega)|^2\,ds\,dP(\omega)$ for its extended nonnegative time-and-sample energy.

For any measure $P$ and a process $H$ with continuous paths for every sample,

$$\int_\Omega|D(H)_t|^2\,dP\le t\,e_t(H).$$

No measurability in the sample variable is required: both sides use nonnegative lower integrals. The bound follows by integrating pathwise Cauchy–Schwarz. It does not by itself claim that the primitive is a measurable random variable; that additional conclusion is supplied under progressiveness.
