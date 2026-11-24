# Moment bound for the running maximum of a time integral

For a real process $H$ indexed by nonnegative time, let

$$D(H)_t(\omega)=\int_0^t H_s(\omega)\,ds.$$

Write $e_T(H)=\int_\Omega\int_{(0,T]}|H_s(\omega)|^2\,ds\,dP(\omega)$ for its extended nonnegative time-and-sample energy.

For any measure $P$ and every-path continuous real process $H$,

$$\int_\Omega\sup_{0\le t\le T}|D(H)_t|^2\,dP\le T\,e_T(H).$$

The statement uses nonnegative lower integrals and therefore does not assume sample measurability. It follows directly from the pathwise uniform Cauchy–Schwarz bound. If the input energy is finite, the displayed running-maximum lower integral is finite as well.
