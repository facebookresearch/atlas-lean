# Global ghost state and ghost ownership

Iris lets a proof use several cameras and allocate fresh instances of them: the resources are defined as a product, over a finite family of cameras, of finite partial maps from ghost names, and ghost ownership $[a : M_i]^{\gamma}$ is ownership of one element at one name in one component.

Let $\mathbf{Camera}$ be the category whose objects are cameras and whose arrows are camera homomorphisms: non-expansive maps $f$ with $f(a) \cdot f(b) = f(a \cdot b)$, $|f(a)| = f(|a|)$, and $n \in \mathcal{V}(a) \Rightarrow n \in \mathcal{V}(f(a))$. Let $(F_i)_{i \in I}$, with $I$ finite, be a family of locally contractive bifunctors $F_i : \mathbf{OFE}^{op} \times \mathbf{OFE} \to \mathbf{Camera}$, local contractiveness being defined as on the [America-Rutten page](../step-indexed-foundations/america-rutten-theorem.md), and let the ghost names be the natural numbers. The *global ghost-state* bifunctor is

$$
F(X^{op}, X) \triangleq \prod_{i \in I} \big(\mathbb{N} \xrightarrow{fin} F_i(X^{op}, X)\big),
$$

where each $F(X^{op}, X)$ carries the operations of the [finite partial function cameras](../cameras/finite-partial-function-camera.md), taken componentwise. Each $F(X^{op}, X)$ is a camera with a unit, the tuple of empty maps, and $F$ is again locally contractive. Hence $G(T) \triangleq \mathrm{UPred}(F(T))$, with $F$ restricted to COFEs, is a locally contractive bifunctor $\mathbf{COFE}^{op} \times \mathbf{COFE} \to \mathbf{COFE}$, because $\mathrm{UPred}$ is a locally non-expansive functor from $\mathbf{Camera}$ to $\mathbf{COFE}$ and the composite of a locally non-expansive functor with a locally contractive bifunctor is locally contractive. As in the source, $F(X)$ abbreviates $F(X, X)$. Let $\mathit{iProp} \cong \mathrm{UPred}(\mathit{Res})$, with $\mathit{Res} \triangleq F(\mathit{iProp}, \mathit{iProp})$, be the solution of the Iris domain equation for this $F$, and put $M_i \triangleq F_i(\mathit{iProp}, \mathit{iProp})$. For $i \in I$, $a \in M_i$ and a name $\gamma \in \mathbb{N}$, *ghost ownership* is

$$
[a : M_i]^{\gamma} \triangleq \mathrm{Own}(r), \qquad r_j \triangleq [\gamma \leftarrow a] \text{ if } j = i, \qquad r_j \triangleq \emptyset \text{ if } j \neq i,
$$

usually written $[a]^{\gamma}$. In the Iris base logic it satisfies, for all $a, b \in M_i$ and $\gamma$:

- if $G \subseteq \mathbb{N}$ is infinite and $a$ is valid at every index, then $\mathrm{True} \vdash \dot{|\!\Rrightarrow} \exists \gamma \in G.\ [a]^{\gamma}$;
- if $a \rightsquigarrow B$ in $M_i$, then $[a]^{\gamma} \vdash \dot{|\!\Rrightarrow} \exists b \in B.\ [b]^{\gamma}$;
- if $\varepsilon$ is a unit of $M_i$, then $\mathrm{True} \vdash \dot{|\!\Rrightarrow} [\varepsilon]^{\gamma}$;
- $[a]^{\gamma} \ast [b]^{\gamma} \dashv\vdash [a \cdot b]^{\gamma}$, and $[a]^{\gamma} \Rightarrow \mathcal{V}(a)$ is derivable;
- if $a$ is a discrete element of $M_i$, that is $a \overset{0}{=} y$ gives $a = y$ for every $y$, then $[a]^{\gamma}$ is timeless.

## Depends on

- [Finite partial function camera](../cameras/finite-partial-function-camera.md)
- [America-Rutten theorem](../step-indexed-foundations/america-rutten-theorem.md)
- [Cameras](../cameras/cameras.md)
- [Frame-preserving updates in cameras](../cameras/camera-frame-preserving-updates.md)
- [Solution of the Iris domain equation](solution-of-the-iris-domain-equation.md)
- [Iris base logic](iris-base-logic.md)
- [Basic update modality](basic-update-modality.md)
- [Except-0 modality and timeless propositions](except-0-modality-and-timeless-propositions.md)

## Proof depends on

- [Finite partial function camera](../cameras/finite-partial-function-camera.md)
- [Frame-preserving updates in cameras](../cameras/camera-frame-preserving-updates.md)
- [Iris base logic](iris-base-logic.md)
- [Except-0 modality and timeless propositions](except-0-modality-and-timeless-propositions.md)

## Expansion

Two facts used above are proved on this page and have no pages of their own. First, a product of finitely many cameras is a camera, with composition, core and validity lifted pointwise, and frame-preserving updates of a component lift to the product (documentation Section 4.1, PROD-UPDATE); so each $F(X^{op}, X)$ is a unital camera. Second, the updates of the finite partial function cameras therefore lift through the product. Two further facts used above are also proved on this page: $\mathrm{UPred}$ is a locally non-expansive functor from $\mathbf{Camera}$ to $\mathbf{COFE}$ (documentation Section 3.3), and the composite of a locally non-expansive (bi)functor with a locally contractive one is locally contractive (documentation Section 2.1, the note after Definition 6); together they give that $G = \mathrm{UPred} \circ F$ is locally contractive, the hypothesis of the solution of the Iris domain equation. The sources derive the rules above from the base-logic rules for $\mathrm{Own}$ and these lifted updates (JFP Section 3.2 for resource algebras, the documentation's Section 7.4 for cameras). The finite maps allow as many instances of each camera as a proof needs, and the product lets proofs that need different cameras be combined by working with a family that contains all of them. For a family of resource algebras, each $F_i$ is constant at the resource algebra viewed as a discrete camera; for higher-order ghost state, JFP states informally that it suffices for the recursive occurrences of $X$ in $F_i$ to be guarded by the later OFE. The documentation names the family $\Sigma_i$ and the product $\mathit{ResF}$, and phrases the construction with a pre-domain $\mathit{iPreProp}$ isomorphic to $\mathit{iProp}$, with $M_i = \Sigma_i(\mathit{iPreProp}, \mathit{iPreProp})$; the JFP article writes $F(\mathit{iProp})$ with the diagonal abbreviation.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 3.2 (the global ghost state as a product of finite maps from ghost names, its unit, the definition of ghost ownership through Own, and the derivation of the ghost-state rules of Figure 4 from Figure 6) and Section 4.7 (the global functor F(X) as a product of finite maps into F_i(X) for a family of functors).
- Iris Team, "The Iris 3.1 documentation", technical documentation (not peer reviewed) that the JFP article cites as its appendix (Iris Team, 2017), version of April 29, 2019, <https://plv.mpi-sws.org/iris/appendix-3.1.pdf>, Section 7.4 (the family of locally contractive bifunctors Sigma_i from OFE^op x OFE to Camera, the resource bifunctor ResF as a product over the family of finite partial functions from GName = N, its unit and local contractiveness, ghost ownership, and the rules RES-ALLOC, RES-UPDATE, RES-EMPTY, RES-OP, RES-VALID and RES-TIMELESS in the forms stated above), Section 4.1 (products over a finite index set, pointwise lifting and PROD-UPDATE), Section 2.4, Definitions 16-17 (camera homomorphisms, the category Camera, and local contractiveness for bifunctors into it), Section 3.3 (UPred is a locally non-expansive functor from Camera to COFE), Section 2.1, the note after Definition 6 (composites of non-expansive and contractive (bi)functors are contractive) and Section 2.1, Definition 2 (discrete elements), supplementary.
