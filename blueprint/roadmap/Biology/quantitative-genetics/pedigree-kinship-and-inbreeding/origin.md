# Founder origin of a gene copy

In a [pedigree](pedigree.md) with parents $(f(i), m(i))$, and for a [gene-dropping outcome](coins.md) $\omega$, the origin of a gene copy $(i, k)$ is defined by recursion on $i$:

- if $i$ is a founder, $o_\omega(i, k) = (i, k)$;
- otherwise $o_\omega(i, k) = o_\omega(p_k, \omega(i, k))$, where $p_0 = f(i)$ and $p_1 = m(i)$.

It is the founder copy from which $(i, k)$ descends.
