# Source local invariant

For a nonarchimedean local field $K$: a local invariant normalized by arithmetic Frobenius
(`NormalizedLocalInvariant`), that is, an isomorphism of abelian groups
$\mathrm{inv} : \mathrm{Br}(K) \to \mathbb{Q}/\mathbb{Z}$ such that, for every finite Galois
extension $E$ of $K$ inside $K^{\mathrm{sep}}$ that is a nonarchimedean local field valuatively
extending $K$, every Frobenius layer on $E$ (`FrobeniusLayer`: $E/K$ is unramified, with an
arithmetic Frobenius $\varphi$ and an isomorphism $\mathrm{Gal}(E/K) \cong \mathbb{Z}/[E:K]$
sending $\varphi$ to $1$) and every uniformizer $\pi$ of $K$, $\mathrm{inv}$ sends to $1/[E:K]$
the class of each two-cocycle whose value at $(g, h)$ is $\pi$ if the Frobenius exponents of $g$
and $h$ on $E$, taken in $\{0, \dots, [E:K] - 1\}$, add up to at least $[E:K]$, and $1$ otherwise
(`primitiveValue`).
