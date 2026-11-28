# Uniform predicates

*Uniform predicates* over a unital camera $M$ are defined as the step-indexed predicates on resources that are upward closed in the resource, identified when they agree on valid resources. They form the semantic domain of Iris propositions and a complete OFE even when $M$ is not complete.

Let $M \xrightarrow{mon,ne} \mathrm{SProp}$ be the OFE of non-expansive $\Phi : M \to \mathrm{SProp}$ such that $a \overset{n}{\preccurlyeq} b$ gives $\Phi(a) \overset{n}{\subseteq} \Phi(b)$, for all $n, a, b$. Define

$$
\mathrm{UPred}(M) \triangleq (M \xrightarrow{mon,ne} \mathrm{SProp}) / \equiv, \qquad \Phi \equiv \Psi \iff \forall m, a.\ m \in \mathcal{V}(a) \Rightarrow (m \in \Phi(a) \Leftrightarrow m \in \Psi(a)),
$$

with $\Phi \overset{n}{=} \Psi \iff \forall m \le n,\ a.\ m \in \mathcal{V}(a) \Rightarrow (m \in \Phi(a) \Leftrightarrow m \in \Psi(a))$. *Semantic entailment* is $\Phi \models \Psi \iff \forall n, a.\ n \in \mathcal{V}(a) \land n \in \Phi(a) \Rightarrow n \in \Psi(a)$. $\mathrm{UPred}(M)$ is a COFE.

## Depends on

- [Cameras](../cameras/cameras.md)
- [Step-indexed propositions](../step-indexed-foundations/step-indexed-propositions.md)
- [Ordered families of equivalences](../step-indexed-foundations/ordered-families-of-equivalences.md)
- [Non-expansive and contractive maps](../step-indexed-foundations/non-expansive-and-contractive-maps.md)
- [Complete ordered families of equivalences](../step-indexed-foundations/complete-ordered-families-of-equivalences.md)

## Proof depends on

- [Cameras](../cameras/cameras.md)
- [Step-indexed propositions](../step-indexed-foundations/step-indexed-propositions.md)
- [Complete ordered families of equivalences](../step-indexed-foundations/complete-ordered-families-of-equivalences.md)

## Expansion

The quotient forgets behaviour on invalid resources, which the logic never observes; because validity is step-indexed, the quotient also changes the step-indexed equality. Upward closure in the resource is what makes the logic affine. The source states completeness in Section 4.5 and stresses that $M$ need not be complete; a limit of a chain $(\Phi_k)$ is given on valid resources by $a \mapsto \{ n \mid n \in \Phi_n(a) \}$. The model is the step-indexed translation of the standard monotone-predicate model of bunched implications.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 4.5 (monotone non-expansive predicates, the quotient UPred(M), its step-indexed equality, completeness and semantic entailment) and Section 4.1.
