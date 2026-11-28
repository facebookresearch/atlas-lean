# Naive higher-order ghost state paradox

Ghost state whose type depends on the type of propositions can make Iris inconsistent, so some restriction on it is necessary: with first-order agreement over propositions one can name a proposition asserting its own falsity.

Let $\mathrm{AG}_0(X)$ be the first-order agreement resource algebra on a set $X$: elements $\mathrm{ag}_0(x)$ and an invalid element, with $\mathrm{ag}_0(x) \cdot \mathrm{ag}_0(y) = \mathrm{ag}_0(x)$ if $x = y$ and every other composition (including any composition with the invalid element) invalid, $|\mathrm{ag}_0(x)| = \mathrm{ag}_0(x)$, and every $\mathrm{ag}_0(x)$ valid.

**Theorem.** Assume the construction of the [global ghost state](../iris-base-logic/global-ghost-state-and-ghost-ownership.md), finite maps from ghost names, can be instantiated with a family of resource algebras in which $\mathrm{AG}_0(\mathit{iProp})$ occurs. Then the view shift $\mathrm{True} \Rrightarrow_{\mathcal{E}} \mathrm{False}$ is derivable.

## Depends on

- [Resource algebras](../resource-algebras.md)
- [Fancy update modality](../invariants-and-logical-atomicity/fancy-update-modality.md)
- [Global ghost state and ghost ownership](../iris-base-logic/global-ghost-state-and-ghost-ownership.md)

## Proof depends on

- [Resource algebras](../resource-algebras.md)
- [Fancy update modality](../invariants-and-logical-atomicity/fancy-update-modality.md)
- [Global ghost state and ghost ownership](../iris-base-logic/global-ghost-state-and-ghost-ownership.md)

## Expansion

The proof uses two derived rules: allocation with a name-dependent initial value, $\mathrm{True} \Rrightarrow_{\mathcal{E}} \exists \gamma.\ [\mathrm{ag}_0(A(\gamma))]^{\gamma}$, from the dependent finite-map allocation update; and agreement, $[\mathrm{ag}_0(P_1)]^{\gamma} \ast [\mathrm{ag}_0(P_2)]^{\gamma} \Rightarrow P_1 = P_2$. With $A(\gamma) \triangleq \exists P.\ \square(P \Rightarrow \mathrm{False}) \ast [\mathrm{ag}_0(P)]^{\gamma}$ and $Q(\gamma) \triangleq [\mathrm{ag}_0(A(\gamma))]^{\gamma}$, one shows $Q(\gamma) \Rightarrow \square(A(\gamma) \Rightarrow \mathrm{False})$ and $Q(\gamma) \Rightarrow A(\gamma)$, and allocation gives False under a view shift. Using $\mathrm{AG}(\blacktriangleright \mathit{iProp})$ weakens agreement to $\triangleright(P_1 = P_2)$ and blocks the argument.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 3.3, Theorem 1 and Lemma 1, with SPROP0-ALLOC, SPROP0-AGREE, GHOST-ALLOC-DEP and FMAP-ALLOC-DEP; Sections 3.1-3.2.
- Iris Team, "The Iris 3.1 documentation", technical documentation (not peer reviewed) that the JFP article cites as its appendix (Iris Team, 2017), version of April 29, 2019, <https://plv.mpi-sws.org/iris/appendix-3.1.pdf>, Section 11.1, Theorem 3 (abstract saved-proposition version), supplementary.
