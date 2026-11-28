# America-Rutten theorem

A locally contractive mixed-variance functor on complete OFEs whose value at the one-point COFE is inhabited has a fixed point, unique up to isomorphism. Iris uses this theorem to construct its type of propositions.

A *bifunctor* $G : \mathbf{COFE}^{op} \times \mathbf{COFE} \to \mathbf{COFE}$ is *locally contractive* if for all COFEs $T_1, T_2$ its action on arrows

$$
G : (T_2 \xrightarrow{ne} T_1) \times (T_1 \xrightarrow{ne} T_2) \to (G(T_1, T_1) \xrightarrow{ne} G(T_2, T_2))
$$

is contractive, the function spaces carrying the pointwise step-indexed equality and the product the componentwise one; it is *locally non-expansive* if this action is non-expansive.

**Theorem (America and Rutten).** Let $1 = \{()\}$ be the discrete COFE on the unit type. If $G : \mathbf{COFE}^{op} \times \mathbf{COFE} \to \mathbf{COFE}$ is a locally contractive bifunctor and $G(1, 1)$ is inhabited, then there is a COFE $T$, unique up to isomorphism, such that $G(T, T) \cong T$ in $\mathbf{COFE}$.

## Depends on

- [Complete ordered families of equivalences](complete-ordered-families-of-equivalences.md)
- [Non-expansive and contractive maps](non-expansive-and-contractive-maps.md)

## Proof depends on

None.

## Expansion

The source states the theorem and cites America and Rutten (1989) and Birkedal, Støvring and Thamsborg (2010) for its proof, which is not reproduced here. It also notes that composing locally non-expansive bifunctors with a locally contractive one gives a locally contractive bifunctor, and that the later functor is locally contractive; these facts are how the theorem is applied to the Iris domain equation. The source's documentation records that uniqueness is not machine checked.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 4.6, Theorem 2 (America and Rutten) with its categorical prerequisites.
- Iris Team, "The Iris 3.1 documentation", technical documentation (not peer reviewed) that the JFP article cites as its appendix (Iris Team, 2017), version of April 29, 2019, <https://plv.mpi-sws.org/iris/appendix-3.1.pdf>, Section 2.2, Theorem 2 and its footnote (uniqueness not proven in Coq), supplementary.
