# Clamped slopes instead of zero end moments change the beam solution

Let $EI > 0$, $L > 0$ and $q \ne 0$, and let $w(x) = q\, x^2 (L - x)^2/(24\, EI)$ be the
[clamped-clamped deflection](clamped-clamped-deflection.md). Then

- $EI\, w''''(x) = q$ for every real $x$;
- $w(0) = w(L) = 0$;
- $w'(0) = w'(L) = 0$ (clamped slopes);

but $w$ does not solve the [simply supported problem](is-simply-supported-solution.md) (its
curvature at $x = 0$ is $q L^2/(12\, EI) \ne 0$), and its midspan deflection differs from that of
the [uniform-load deflection](../euler-bernoulli-beam-under-uniform-load/uniform-load-deflection.md)
of the simply supported beam: $w(L/2) = q L^4/(384\, EI)$ against $5 q L^4/(384\, EI)$. So replacing
the two zero-moment conditions by clamped slopes gives a different solution.
