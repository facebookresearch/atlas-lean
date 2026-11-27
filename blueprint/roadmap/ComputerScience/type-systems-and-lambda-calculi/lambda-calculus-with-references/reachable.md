# Configurations on the evaluation path of Landin's knot

Let $K$ be Landin's knot,
$\iota = \lambda x{:}\mathrm{Unit}.\,x$, $b_0 = \lambda x{:}\mathrm{Unit}.\,(!\ell_0)\,x$ with
$\ell_0$ the store location $0$, $a = (!\ell_0)\ \mathrm{unit}$, $b = b_0\ \mathrm{unit}$,
$c_1$ the term $K$ with its argument $\mathrm{ref}\ \iota$ replaced by $\ell_0$,
$c_2 = (\lambda y{:}\mathrm{Unit}.\,a)\,(\ell_0 := b_0)$ and
$c_3 = (\lambda y{:}\mathrm{Unit}.\,a)\ \mathrm{unit}$; write $[\,]$ for the empty store and
$[t]$ for the store whose only location $\ell_0$ holds $t$. This is the list of the six
configurations (term, store) $(K, [\,])$, $(c_1, [\iota])$, $(c_2, [\iota])$, $(c_3, [b_0])$,
$(a, [b_0])$, $(b, [b_0])$.

Each configuration steps to the next and $(b, [b_0])$ steps back to $(a, [b_0])$; every
configuration reachable from $(K, [\,])$ lies in this list.
