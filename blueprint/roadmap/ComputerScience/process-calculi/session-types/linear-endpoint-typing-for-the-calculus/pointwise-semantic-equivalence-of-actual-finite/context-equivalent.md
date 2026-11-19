# Pointwise equivalence of ownership maps

Two capabilities $c = (k,S)$ and $d = (k',S')$ are equivalent, $c \approx d$, when $k = k'$ and $S$
and $S'$ denote the same protocol tree, i.e. they are bisimilar for the transitions given by
protocol heads (a name send or receive leads to its continuation; an endpoint send or receive,
labelled with its polarity and rank, leads separately to its payload and to its continuation). Two
ownership contexts $\Delta$ and $\Xi$ are equivalent, $\Delta \approx \Xi$, when for every endpoint
$e$ either neither context has an entry at $e$, or $\Delta(e) = c$ and $\Xi(e) = d$ with $c \approx
d$.
