# Search finds the first matching represented identity

If a node pool represents, from the
head $h$, the list of distinct identities $\ell$, then for every target payload $t$ the search
for $t$ from $h$ returns the first identity in $\ell$ whose cell holds a node with payload $t$,
and returns nothing if no identity in $\ell$ has this property.
