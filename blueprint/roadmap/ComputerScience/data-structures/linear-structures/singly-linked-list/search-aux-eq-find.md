# Fuel-bounded search finds the first matching represented identity

Suppose a node pool
represents, from the head $h$, the list of distinct identities $\ell$. Then for every target
payload $t$ and every fuel $f$ with $f \ge |\ell|$, fuel-bounded search for $t$ from $h$ with
fuel $f$ returns the first identity in $\ell$ whose cell holds a node with payload $t$, and
returns nothing if no identity in $\ell$ has this property.
