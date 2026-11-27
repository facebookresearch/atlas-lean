# Special soundness

Let $G$ be a commutative group, $q$ a prime and $g, y \in G$ with
$g^q = 1$ and $y^q = 1$; for $h \in G$ and $a \in \mathbb{Z}/q$ write $h^a$ for $h^{\bar a}$,
where $\bar a \in \{0, \dots, q - 1\}$ is the representative of $a$. Let $I \in G$ and
$r, s, r', s' \in \mathbb{Z}/q$ with $r \ne r'$, and suppose both transcripts $(I, r, s)$ and
$(I, r', s')$ are accepted, that is, $g^s (y^r)^{-1} = I$ and $g^{s'} (y^{r'})^{-1} = I$. Then
the extracted exponent $e = (s - s')(r - r')^{-1}$ is a discrete logarithm of $y$: $g^e = y$.
