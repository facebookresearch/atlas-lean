# Cuckoo insertion stores the inserted binding

Let $T$ be a cuckoo hash table with hash
functions $h_1$ and $h_2$. If inserting (or replacing) the binding $k \mapsto v$ in $T$ with fuel
$f$ succeeds and returns the table $T'$, then the binding $k \mapsto v$ is stored in some slot of
either table of $T'$.
