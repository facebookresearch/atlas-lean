# Basic update modality

The *basic update modality* is defined as the uniform predicate stating that the owned resources can be changed, by a frame-preserving update that respects every frame, into resources satisfying a given predicate.

On $\mathrm{UPred}(M)$ for a unital camera $M$,

$$
(\dot{|\!\Rrightarrow} P)(a) \triangleq \{ n \mid \forall m \le n,\ c.\ m \in \mathcal{V}(a \cdot c) \Rightarrow \exists b.\ m \in \mathcal{V}(b \cdot c) \land m \in P(b) \}.
$$

## Depends on

- [Uniform predicates](uniform-predicates.md)
- [Cameras](../cameras/cameras.md)

## Proof depends on

None.

## Expansion

The base logic's rules for this modality are UPD-MONO, UPD-INTRO, UPD-TRANS, UPD-FRAME and UPD-UPDATE (from $a \rightsquigarrow B$ infer $\mathrm{Own}(a) \vdash \dot{|\!\Rrightarrow} \exists b \in B.\ \mathrm{Own}(b)$); they say the modality is a strong monad for separating conjunction that internalises frame-preserving updates, and their validity in this model is part of the soundness of the Iris semantic model. The quantifier over frames $c$ is what makes the modality respect resources owned by others.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 5.4 (definition and intuition of the basic update modality), Figure 10 (interpretation) and Figure 11 (UPD-MONO, UPD-INTRO, UPD-TRANS, UPD-FRAME, UPD-UPDATE).
