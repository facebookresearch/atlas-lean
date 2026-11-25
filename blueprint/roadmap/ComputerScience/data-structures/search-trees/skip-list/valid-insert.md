# Insertion preserves skip-list validity

Let $\alpha$ be a linearly ordered type and
$\beta$ a type. If a skip list with keys in $\alpha$ and values in $\beta$ is valid, then for every
key $k \in \alpha$, value $v \in \beta$ and requested height $h \in \mathbb{N}$ (including
$h = 0$), inserting $k$ with value $v$ and requested height $h$ yields a valid skip list. This
covers both a new key and a key already present, whose value is replaced.
