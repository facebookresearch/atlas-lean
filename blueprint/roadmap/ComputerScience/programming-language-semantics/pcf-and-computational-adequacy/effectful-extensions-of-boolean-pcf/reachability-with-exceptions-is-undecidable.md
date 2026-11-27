# Reachability for Boolean PCF with exceptions is undecidable

Adding exceptions to Boolean PCF makes it undecidable whether a closed program reaches the error command; the source re-proves Lillibridge's result with exceptions that carry only first-order functions.

**Theorem.** Extend [Boolean PCF](boolean-pcf-and-its-reachability-problem.md) with one exception constructor $\mathbf{Ex}_\tau$ for each type $\tau$, expressions $\mathbf{raise}_\tau\, M$ (of any type, for $M : \tau$) and $\mathbf{try}_\tau\ M_1\ \mathbf{with}\ \mathbf{Ex}_\tau\, x \to M_2$, and the reduction rule

$$
E[\mathbf{try}_\tau\ E'[\mathbf{raise}_\tau\, V]\ \mathbf{with}\ \mathbf{Ex}_\tau\, x \to M] \longrightarrow E[M[V/x]]
$$

when $E'$ contains no handler for $\mathbf{Ex}_\tau$ around the hole. The reachability problem for this language is undecidable.

## Depends on

- [Boolean PCF and its reachability problem](boolean-pcf-and-its-reachability-problem.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Lillibridge proved the result, even without recursion, by encoding the untyped λ-calculus with exceptions carrying second-order functions of type $(\mathbf{unit} \to \mathbf{unit}) \to (\mathbf{unit} \to \mathbf{unit})$. The source's alternative proof reduces from the halting problem of Minsky machines and uses recursion but only exceptions carrying first-order functions of type $\mathbf{unit} \to \mathbf{unit}$, so the two fragments are incomparable. Each counter value $n$ is a function $c$ of type $\mathbf{unit} \to \mathbf{unit}$. Incrementing builds $\lambda x.\,\mathbf{raise}\ c$ from the old counter $c$; a zero test or decrement runs the counter inside a handler, and the counter for $0$ returns normally while a positive counter raises its predecessor, which the handler binds. A halting instruction becomes $\mathbf{fail}$, so the machine halts iff the encoding reaches $\mathbf{fail}$. The source notes that an exception carrying an exception-raising closure is essential: if exceptions carry only base-type values the problem is decidable.

## Sources

- Naoki Kobayashi, "On Decidable and Undecidable Extensions of Simply Typed Lambda Calculus", *Proceedings of the ACM on Programming Languages* 9(POPL), 2025, pp. 1136–1166, <https://doi.org/10.1145/3704875>; read as arXiv:2411.06086v2, <https://arxiv.org/abs/2411.06086v2>: the subsection "Boolean PCF with Exceptions" of the section "Undecidable Extensions of Boolean PCF", with its theorem and Minsky-machine encoding, of that version.
