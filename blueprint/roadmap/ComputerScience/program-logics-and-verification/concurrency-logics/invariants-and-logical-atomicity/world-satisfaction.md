# World satisfaction

*World satisfaction* $W$ is defined as the single global assertion that keeps a registry of all Iris invariants and keeps each enabled invariant's content one step later. Invariant assertions are fragments of that registry, and namespaces give each family of invariants infinitely many names.

Instantiate Iris, through the [global ghost state](../iris-base-logic/global-ghost-state-and-ghost-ownership.md), with the cameras $\mathrm{INV} = \mathrm{AUTH}(\mathbb{N} \xrightarrow{fin} \mathrm{AG}(\blacktriangleright \mathit{iProp}))$, $\mathrm{EN} = \wp(\mathbb{N})$ and $\mathrm{DIS} = \wp^{fin}(\mathbb{N})$, the last two composing by disjoint union with an invalid element for overlapping sets, at fixed ghost names $\gamma_{\mathrm{INV}}, \gamma_{\mathrm{EN}}, \gamma_{\mathrm{DIS}}$. Define

$$
W \triangleq \exists I : \mathbb{N} \xrightarrow{fin} \mathit{iProp}.\ [\bullet\, \mathrm{ag}(\mathrm{next}(I))]^{\gamma_{\mathrm{INV}}} \ast \mathop{\ast}_{\iota \in \mathrm{dom}(I)} \big( (\triangleright I(\iota) \ast [\{\iota\}]^{\gamma_{\mathrm{DIS}}}) \lor [\{\iota\}]^{\gamma_{\mathrm{EN}}} \big),
$$

$$
\boxed{P}^{\iota} \triangleq [\circ\, [\iota \leftarrow \mathrm{ag}(\mathrm{next}(P))]]^{\gamma_{\mathrm{INV}}}, \qquad \boxed{P}^{\mathcal{N}} \triangleq \exists \iota \in \mathcal{N}^{\uparrow}.\ \boxed{P}^{\iota},
$$

where $\mathrm{ag}$ and $\mathrm{next}$ act pointwise on $I$, a namespace $\mathcal{N}$ is a list of natural numbers, and $\mathcal{N}^{\uparrow} = \{ f(\mathcal{N}') \mid \mathcal{N}' \text{ a sub-namespace of } \mathcal{N} \}$ for a fixed injection $f : \mathrm{List}(\mathbb{N}) \to \mathbb{N}$. World satisfaction satisfies

- $\boxed{P}^{\iota} \vdash \square \boxed{P}^{\iota}$ and $[\bullet\, \mathrm{ag}(\mathrm{next}(I))]^{\gamma_{\mathrm{INV}}} \ast \boxed{P}^{\iota} \vdash \triangleright I(\iota) \Leftrightarrow \triangleright P$;
- for infinite $\mathcal{E} \subseteq \mathbb{N}$, the proposition $W \ast \triangleright P \mathrel{-\!\!\ast} \dot{|\!\Rrightarrow} (W \ast \exists \iota \in \mathcal{E}.\ \boxed{P}^{\iota})$ is derivable;
- $\boxed{P}^{\iota} \vdash (W \ast [\{\iota\}]^{\gamma_{\mathrm{EN}}}) \Leftrightarrow (W \ast \triangleright P \ast [\{\iota\}]^{\gamma_{\mathrm{DIS}}})$.

## Depends on

- [Authoritative camera](../cameras/authoritative-camera.md)
- [Higher-order agreement camera](../cameras/higher-order-agreement-camera.md)
- [Finite partial function camera](../cameras/finite-partial-function-camera.md)
- [Later OFE](../step-indexed-foundations/later-ofe.md)
- [Solution of the Iris domain equation](../iris-base-logic/solution-of-the-iris-domain-equation.md)
- [Iris base logic](../iris-base-logic/iris-base-logic.md)
- [Basic update modality](../iris-base-logic/basic-update-modality.md)
- [Global ghost state and ghost ownership](../iris-base-logic/global-ghost-state-and-ghost-ownership.md)

## Proof depends on

- [Authoritative camera](../cameras/authoritative-camera.md)
- [Higher-order agreement camera](../cameras/higher-order-agreement-camera.md)
- [Finite partial function camera](../cameras/finite-partial-function-camera.md)
- [Basic update modality](../iris-base-logic/basic-update-modality.md)
- [Iris base logic](../iris-base-logic/iris-base-logic.md)
- [Global ghost state and ghost ownership](../iris-base-logic/global-ghost-state-and-ghost-ownership.md)

## Expansion

The authoritative element records the full map of registered invariants and each fragment witnesses one entry; agreement makes every witness agree with the registry, but only under a later because the camera stores later-guarded propositions. Each registered invariant is either enabled (W owns its content and the disabled token) or disabled (W owns the enabled token); a thread holding the enabled token can trade it for the content and the disabled token. Allocation chooses a name in $\mathcal{E}$ not in the registry for which a disabled token can be created, which exists because only finitely many disabled tokens exist.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 7.1.1 and Figure 14 (cameras INV, EN, DIS, world satisfaction, invariant assertions, INVREG-PERSIST, INVREG-AGREE with the bi-implication between the two later propositions, INVREG-ALLOC, WSAT-ALLOC, WSAT-OPENCLOSE) and Section 7.1.2 (namespaces).
