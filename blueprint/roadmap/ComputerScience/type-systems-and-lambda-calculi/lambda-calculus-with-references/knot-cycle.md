# The cycle of Landin's knot

Write $\ell_0$ for store location $0$, let
$b_0 = \lambda x{:}\mathrm{Unit}.\ (!\ell_0)\,x$, and let $[b_0]$ be the store whose only entry, at
$\ell_0$, is $b_0$. In one call-by-value step, $(!\ell_0)\,\mathrm{unit}$ with store $[b_0]$ steps
to $b_0\,\mathrm{unit}$ with store $[b_0]$, and in one further step $b_0\,\mathrm{unit}$ with store
$[b_0]$ steps back to $(!\ell_0)\,\mathrm{unit}$ with store $[b_0]$.
