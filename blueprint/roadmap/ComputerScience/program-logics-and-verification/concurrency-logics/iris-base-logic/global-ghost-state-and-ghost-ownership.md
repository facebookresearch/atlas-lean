# Global ghost state and ghost ownership

Iris lets a proof use several cameras and allocate fresh instances of them: the resources are defined as a product, over a finite family of cameras, of finite partial maps from ghost names, and ghost ownership $[a : M_i]^{\gamma}$ is ownership of one element at one name in one component.

Let $(F_i)_{i \in I}$ be a finite family that assigns to each OFE $X$ a camera $F_i(X)$, and let the ghost names be the natural numbers. The *global ghost-state* camera is

$$
F(X) \triangleq \prod_{i \in I} \big(\mathbb{N} \xrightarrow{fin} F_i(X)\big),
$$

with the operations of the [finite partial function cameras](../cameras/finite-partial-function-camera.md) taken componentwise; it is a unital camera whose unit is the tuple of empty maps. Assume $G(T) \triangleq \mathrm{UPred}(F(T))$ is a locally contractive bifunctor, let $\mathit{iProp} \cong \mathrm{UPred}(\mathit{Res})$ with $\mathit{Res} = F(\mathit{iProp})$ be the solution of the Iris domain equation, and put $M_i \triangleq F_i(\mathit{iProp})$. For $i \in I$, $a \in M_i$ and a name $\gamma \in \mathbb{N}$, *ghost ownership* is

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

The sources derive these rules from the base-logic rules for $\mathrm{Own}$ and the frame-preserving updates of the finite maps lifted to the product (JFP Section 3.2 for resource algebras, the documentation's Section 7.4 for cameras). The finite maps allow as many instances of each camera as a proof needs, and the product lets proofs that need different cameras be combined by working with a family that contains all of them. For a family of resource algebras, each $F_i$ is constant at the resource algebra viewed as a discrete camera; for higher-order ghost state, the source states informally that it suffices for the recursive occurrences of $X$ in $F_i(X)$ to be guarded by the later OFE for $G$ to be locally contractive. The documentation phrases the construction with a pre-domain $\mathit{iPreProp}$ isomorphic to $\mathit{iProp}$, with $M_i = F_i(\mathit{iPreProp})$; the JFP article writes $F(\mathit{iProp})$.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 3.2 (the global ghost state as a product of finite maps from ghost names, its unit, the definition of ghost ownership through Own, and the derivation of the ghost-state rules of Figure 4 from Figure 6) and Section 4.7 (the global functor F(X) as a product of finite maps into F_i(X) for a family of functors).
- Iris Team, "The Iris 3.1 documentation", technical documentation (not peer reviewed) that the JFP article cites as its appendix (Iris Team, 2017), version of April 29, 2019, <https://plv.mpi-sws.org/iris/appendix-3.1.pdf>, Section 7.4 (the resource functor as a product over the family of finite partial functions from GName = N, its unit, ghost ownership, and the rules RES-ALLOC, RES-UPDATE, RES-EMPTY, RES-OP, RES-VALID and RES-TIMELESS in the forms stated above), Section 4.1 (products over a finite index set) and Section 2.1, Definition 2 (discrete elements), supplementary.
