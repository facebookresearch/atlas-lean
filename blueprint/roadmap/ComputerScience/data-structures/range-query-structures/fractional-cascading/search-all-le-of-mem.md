# Search positions are boundary indices

Let $x$ be a value and let $cs$ be a list of
catalogs whose entry at index $i$ is the catalog $c$. Then searching every catalog of $cs$ for
$x$ gives, at index $i$, the lower bound of $x$ in $c$ (the number of elements of $c$ that are
$< x$), and this lower bound is at most the length of $c$.
