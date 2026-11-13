# Aj Map

The **Aalen–Johansen map** on cell vectors, up to the horizon `m`: coordinate `(none, j)` is
the product-limit survival `∏_{l ≤ j} factor u l`, and coordinate `(some c, j)` is the cumulative
incidence `∑_{l ≤ j} (∏_{i < l} factor u i) · u_{l,c} / u_l`. The ratios are scale invariant, so
on the empirical mean cell vector it gives the Kaplan–Meier and Aalen–Johansen estimates
(`ajMap_empiricalMean`).
