# Declared signature offers survive one reduction step

Let $\Gamma$ be a service environment (a finite map from natural numbers to service signatures), $s$
a natural number, $\sigma$ a service signature and $p$, $q$ processes with $p \to q$. If $p$ offers
$s$ with signature $\sigma$, that is $\Gamma(s) = \sigma$ and $p$ offers $\mathrm{c}_s$ persistently
(it contains, under parallel compositions and restrictions only, a replication whose body has an
unguarded input on $\mathrm{c}_s$), then $q$ offers $s$ with signature $\sigma$.
