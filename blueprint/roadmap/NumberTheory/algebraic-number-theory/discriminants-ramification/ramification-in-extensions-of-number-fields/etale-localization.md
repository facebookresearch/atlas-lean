# Localizing the ring of integers at an unramified prime gives an étale algebra

Let $K$ be
a number field with ring of integers $\mathcal{O}_K$, and let $p$ be a prime ideal of $\mathbb{Z}$
that is unramified in $\mathcal{O}_K$, that is, every prime ideal of $\mathcal{O}_K$ lying over $p$
is unramified over $\mathbb{Z}$. Let $S$ be the localization of $\mathcal{O}_K$ at the image of
the multiplicative set $\mathbb{Z} \setminus p$. Then $S$ is an étale algebra over the local ring
$\mathbb{Z}_{(p)}$.

The ring $S$ is semilocal: it keeps every prime of $\mathcal{O}_K$ above $p$ at once, rather than
the localization $(\mathcal{O}_K)_Q$ at a single such prime $Q$.

## Sources

- packages the primewise unramified hypothesis used by `isUnramifiedAtPrime_sup` in the primary Lean source for ATLAS `NumberTheoryI` target N390, Proposition 19.14.
