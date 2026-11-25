# Cycle term of Landin's knot

The term $(!\ell_0)\ \mathrm{unit}$: the dereference of
the store location $\ell_0$ (location $0$), applied to the unit value.

When $\ell_0$ holds $b_0 = \lambda x{:}\mathrm{Unit}.\,(!\ell_0)\,x$, this term steps to
$b_0\ \mathrm{unit}$, which steps back to it; these are the two configurations of the cycle.
