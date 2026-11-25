# Source corestriction

For a finite extension $L/K$ of fields, with absolute Galois groups $G_L$ and $G_K$, a
$K$-embedding $\sigma : L \to K^{\mathrm{sep}}$ and Galois data $P$ for $\sigma$
(`FiniteFieldPair`): a corestriction $\mathrm{cor} : \mathrm{Br}(L) \to \mathrm{Br}(K)$ given on
cocycles by the transfer formula (`NormalizedCorestriction`), that is, an additive map such that,
for every left transversal $t$ of the subgroup of $G_K$ fixing $\sigma(L)$ and every continuous
two-cocycle $c$ of $G_L$ with values in $(L^{\mathrm{sep}})^\times$, $\mathrm{cor}$ sends the class
of $c$ to the class of a two-cocycle of $G_K$ whose inhomogeneous values are those of the transfer
of $c$ along $t$ (`transferValue`).
