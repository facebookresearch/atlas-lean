# Translation of System F terms into Fω

For a map $\varphi$ assigning to each $i < n$ a type $\varphi(i) \in \mathrm{Ty}^{\star}_{\Delta}$,
the translation $\mathcal{T}_\varphi(t) \in \mathrm{Tm}_{\Delta,m}$ of a [System F
term](../../system-f/scoped-pure-system-f/tm.md) $t \in \mathrm{Tm}_{n,m}$ is defined by
$\mathcal{T}_\varphi(x_i) = x_i$, $\mathcal{T}_\varphi(\lambda A.\,b) =
\lambda\mathcal{T}_\varphi(A).\, \mathcal{T}_\varphi(b)$, $\mathcal{T}_\varphi(f\,a) =
\mathcal{T}_\varphi(f)\,\mathcal{T}_\varphi(a)$, $\mathcal{T}_\varphi(\Lambda b) =
\Lambda_\star\,\mathcal{T}_{\varphi^{\uparrow}}(b)$ and $\mathcal{T}_\varphi(f\,[A]) =
\mathcal{T}_\varphi(f)\,[\mathcal{T}_\varphi(A)]$, using the [type translation](from-system-f.md) on
annotations.
