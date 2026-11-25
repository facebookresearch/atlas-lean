# Binder extension preserves fixing of shared constants

Let $\Gamma$ be a service environment and $f$ a map from names to names with $f(\mathrm{c}_s) =
\mathrm{c}_s$ for every $s$ declared in $\Gamma$. Then its extension under one binder $f^{\uparrow}$
(which fixes $\mathrm{v}_0$ and sends $\mathrm{c}_a$, $\mathrm{v}_{i+1}$ to $\uparrow_0
f(\mathrm{c}_a)$, $\uparrow_0 f(\mathrm{v}_i)$) also fixes every declared $\mathrm{c}_s$.
