# Landin's knot

The term

$$
(\lambda r{:}\mathrm{Ref}\,(\mathrm{Unit}\to\mathrm{Unit}).\ (\lambda y{:}\mathrm{Unit}.\ (!r)\,
\mathrm{unit})\ (r := \lambda x{:}\mathrm{Unit}.\ (!r)\,x))
\ (\mathrm{ref}\,(\lambda x{:}\mathrm{Unit}.\ x))
$$

of the simply typed lambda calculus with references.

It allocates a cell $r$ holding the identity on $\mathrm{Unit}$, overwrites it with a function that
calls whatever $r$ holds, and then calls the contents of $r$ on $\mathrm{unit}$: a recursive knot
tied through the store.
