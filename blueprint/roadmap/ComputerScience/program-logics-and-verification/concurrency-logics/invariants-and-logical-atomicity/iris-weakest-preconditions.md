# Iris weakest preconditions

The *weakest precondition* $\mathrm{wp}^S_{\mathcal{E}}\ e\ \{\Phi\}$ of the Iris program logic is defined by guarded recursion: either $e$ is a value satisfying $\Phi$ after a fancy update, or for every state described by the state interpretation $S$, $e$ is reducible and every step, one later, re-establishes $S$, the weakest precondition of the result and of every forked thread.

A *language* consists of a set $\mathrm{Expr}$ of expressions, a set $\mathrm{Val} \subseteq \mathrm{Expr}$ of values, a set $\mathrm{State}$ of states and a per-thread step relation $(\to_t) \subseteq (\mathrm{Expr} \times \mathrm{State}) \times (\mathrm{Expr} \times \mathrm{State} \times \mathrm{List}(\mathrm{Expr}))$ such that only non-values step: $(e, \sigma) \to_t (e', \sigma', \vec{e}_f)$ requires $e \notin \mathrm{Val}$; $\mathrm{red}(e, \sigma)$ means that $(e, \sigma)$ can take a step. Given a *state interpretation* $S : \mathrm{State} \to \mathit{iProp}$, define in the Iris base logic, as a guarded fixed point,

$$
\mathrm{wp}^S_{\mathcal{E}}\ e\ \{\Phi\} \triangleq (e \in \mathrm{Val} \wedge |\!\Rrightarrow_{\mathcal{E}} \Phi(e)) \vee \Big(e \notin \mathrm{Val} \wedge \forall \sigma.\ S(\sigma) \mathrel{-\!\!\ast} {}^{\mathcal{E}}|\!\Rrightarrow^{\emptyset} \big(\mathrm{red}(e, \sigma) \wedge \triangleright \forall e_2, \sigma_2, \vec{e}_f.\ ((e, \sigma) \to_t (e_2, \sigma_2, \vec{e}_f)) \mathrel{-\!\!\ast} {}^{\emptyset}|\!\Rrightarrow^{\mathcal{E}} (S(\sigma_2) \ast \mathrm{wp}^S_{\mathcal{E}}\ e_2\ \{\Phi\} \ast \mathop{\ast}_{e' \in \vec{e}_f} \mathrm{wp}^S_{\top}\ e'\ \{v.\, \mathrm{True}\})\big)\Big),
$$

where $\top$ is the full mask. Hoare triples are $\{P\}\ e\ \{\Phi\}^S_{\mathcal{E}} \triangleq \square (P \mathrel{-\!\!\ast} \mathrm{wp}^S_{\mathcal{E}}\ e\ \{\Phi\})$.

## Depends on

- [Fancy update modality](fancy-update-modality.md)
- [Iris base logic](../iris-base-logic/iris-base-logic.md)
- [Guarded fixed points](../iris-base-logic/guarded-fixed-points-of-uniform-predicates.md)

## Proof depends on

- [Guarded fixed points](../iris-base-logic/guarded-fixed-points-of-uniform-predicates.md)

## Expansion

The recursive occurrences are under $\triangleright$, so the definition is a well-defined guarded fixed point; this ties each program step to one step index. The outer mask $\mathcal{E}$ gives the fancy updates access to the invariants in $\mathcal{E}$, the inner masks are empty so that reasoning about a single step may open all invariants, and every invariant must be closed again after each physical step, which is why invariants can only be opened around atomic expressions. Forked threads get the full mask. For the ML-like language with heaps, $S(\sigma) = [\bullet \sigma]^{\gamma_{\mathrm{HEAP}}}$ in the authoritative heap camera recovers the earlier definition. JFP Theorem 7 states adequacy for this generic definition, with the state interpretation chosen under a fancy update; [adequacy of Iris weakest preconditions](../adequacy-of-iris-weakest-preconditions.md) states the adequacy theorem for the concrete language of JFP Section 6.1 (Theorem 6).

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 7.3 and Figure 14 (language interface, state interpretation, the weakest precondition and Hoare triples) and Sections 6.3.1-6.3.4 (the construction in stages and the role of the later).
