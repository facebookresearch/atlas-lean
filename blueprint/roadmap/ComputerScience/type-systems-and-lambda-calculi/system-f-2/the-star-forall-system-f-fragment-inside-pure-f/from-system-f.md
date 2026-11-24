# Translation of System F types into Fω

For a kinding context $\Delta$ and a map $\varphi$ assigning to each $i < n$ a type $\varphi(i) \in
\mathrm{Ty}^{\star}_{\Delta}$, the translation $\mathcal{T}_\varphi(A) \in
\mathrm{Ty}^{\star}_{\Delta}$ of a [System F type](../../system-f/scoped-pure-system-f/ty.md) $A \in
\mathrm{Ty}_n$ is defined by $\mathcal{T}_\varphi(\alpha_i) = \varphi(i)$, $\mathcal{T}_\varphi(A
\to B) = \mathcal{T}_\varphi(A) \to \mathcal{T}_\varphi(B)$ and $\mathcal{T}_\varphi(\forall B) =
\forall_\star\,\mathcal{T}_{\varphi^{\uparrow}}(B)$, with the [lifted map](lift-types.md)
$\varphi^{\uparrow}$. System F quantifiers become quantifiers over kind $\star$.
