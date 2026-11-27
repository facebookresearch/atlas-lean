# Hypertrace logic with constrained and unconstrained trace quantifiers

Hypertrace logic is a two-sorted first-order logic over time points in $\mathbb{N}$ and infinite traces, with binary predicates relating a trace and a time; constrained trace quantifiers range over the traces of the model, unconstrained ones over all traces.

**Syntax.** Fix a finite set $\mathbb{X}$ of binary predicates (one per atomic proposition), trace variables $\pi$ and time variables $i$. Formulas are

$$
\varphi ::= \exists \pi\, \varphi \mid \exists \pi \mathbin{::} T\, \varphi \mid \exists i\, \varphi \mid \neg\varphi \mid \varphi \vee \varphi \mid i < i \mid i = i \mid a(\pi, i)
$$

with $a \in \mathbb{X}$; $\exists \pi \mathbin{::} T\, \varphi$ abbreviates $\exists \pi\, (T(\pi) \wedge \varphi)$ for a unary trace predicate $T$, and universal quantifiers are the duals.

**Semantics.** A trace is an infinite word over $2^{\mathbb{X}}$, time variables range over $(\mathbb{N}, <)$, and $a(\pi, i)$ holds when $a$ is in the $i$-th letter of the trace assigned to $\pi$. A set $\mathcal{T}$ of traces is a model of $\varphi$ if $\varphi$ holds when $T$ is interpreted as $\mathcal{T}$: unconstrained quantifiers $\exists \pi$ range over all traces and constrained quantifiers $\exists \pi \mathbin{::} T$ over the traces in $\mathcal{T}$. $[\![\varphi]\!]$ is the set of models of $\varphi$, and the *satisfiability problem* asks whether $[\![\varphi]\!] \ne \varnothing$. A formula is *time-prefixed* if all its time quantifiers precede all its trace quantifiers, and *trace-prefixed* in the opposite case. With constrained trace quantifiers only, trace-prefixed formulas correspond to [HyperLTL](hyperltl.md)-style specifications.

## Depends on

- [HyperLTL](hyperltl.md)

## Proof depends on

None.

## Sources

- Marek Chalupa, Thomas A. Henzinger and Ana Oliveira da Costa, "Flavors of quantifiers in hyperlogics", in *45th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2025)*, LIPIcs 360, 20:1–20:18, 2025, doi:[10.4230/LIPIcs.FSTTCS.2025.20](https://doi.org/10.4230/LIPIcs.FSTTCS.2025.20). Numbering of the version read, arXiv:2510.12298v1: Section 3.1 (syntax and semantics of hypertrace logic, grammar (5)).
