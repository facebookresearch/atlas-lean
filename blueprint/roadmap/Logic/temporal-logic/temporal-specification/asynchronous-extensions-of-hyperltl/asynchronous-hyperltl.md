# Asynchronous HyperLTL

Asynchronous HyperLTL (AHLTL) quantifies over traces and then over a trajectory, which decides at each step which of the quantified traces advance, so that the traces can be compared asynchronously.

**Definition.** Traces are infinite words over $2^{AP}$. A *transition system* $\mathcal T = (V, E, I, \ell)$ has a nonempty finite set $V$ of vertices and a nonempty set $I \subseteq V$ of initial vertices, every vertex has a successor, and $\mathrm{Tr}(\mathcal T)$ is the set of label sequences of its runs from initial vertices. AHLTL formulas are

$$
\varphi ::= \exists x\,\varphi \mid \forall x\,\varphi \mid \mathsf E\psi \mid \mathsf A\psi, \qquad \psi ::= p_x \mid \neg\psi \mid \psi \vee \psi \mid \mathsf X\psi \mid \psi\,\mathsf U\,\psi,
$$

with trace variables $x$ and $p \in AP$. A *trajectory* for $\psi$ is an infinite sequence $t(0)t(1)\cdots$ of nonempty subsets of the trace variables of $\psi$; a *pointer assignment* maps each variable to its current position, starting at $0$, and step $i$ of the trajectory advances exactly the pointers of the variables in $t(i)$. For a set $L$ of traces, $\exists x$ and $\forall x$ range over $L$; $\mathsf E\psi$ holds if $\psi$ holds at step $0$ for some trajectory and $\mathsf A\psi$ if for all; $p_x$ holds if $p$ belongs to the trace bound to $x$ at the current pointer of $x$; and $\mathsf X$, $\mathsf U$ move along the trajectory, advancing pointers as it dictates. A sentence has no free variables; *E-AHLTL* and *A-AHLTL* are the sentences with $\mathsf E$ and with $\mathsf A$. A nonempty set $L$ satisfies a sentence if it holds with the empty assignment, and $\mathcal T \models \varphi$ if $\mathrm{Tr}(\mathcal T)$ satisfies $\varphi$. *Satisfiability* asks whether some nonempty set of traces satisfies $\varphi$, *finite-state satisfiability* whether some transition system does, and *model checking* whether a given $\mathcal T$ satisfies $\varphi$.

## Depends on

- [HyperLTL](../hyperltl.md)

## Proof depends on

None.

## Expansion

AHLTL was introduced by Baumeister, Coenen, Bonakdarpour, Finkbeiner and Sánchez; the definition here updates pointers instead of trace suffixes and is equivalent. The formula $\forall x\,\forall x'\,\mathsf E\,(\ell_x \leftrightarrow \ell_{x'}) \to \mathsf G(\ell_x \leftrightarrow \ell_{x'})$ expresses observational determinism for asynchronous systems. HyperLTL embeds into AHLTL with an additional proposition. Every satisfiable AHLTL sentence has a countable model (Theorem 1 of the source).

## Sources

- G. Regaud and M. Zimmermann, "The Complexity of Asynchronous HyperLTL", *Electronic Proceedings in Theoretical Computer Science* 454, 2026, pp. 183–199, <https://doi.org/10.4204/EPTCS.454.13>; read as arXiv:2606.06091v2, <https://arxiv.org/abs/2606.06091v2>: Section 2 (transition systems, Section 2.1 syntax and semantics, Remarks 1 and 2), Theorem 1 in Section 3, and Section 1.
- J. Baumeister, N. Coenen, B. Bonakdarpour, B. Finkbeiner and C. Sánchez, "A Temporal Logic for Asynchronous Hyperproperties", in *Computer Aided Verification (CAV 2021), Part I*, Lecture Notes in Computer Science 12759, Springer, 2021, pp. 694–717, <https://doi.org/10.1007/978-3-030-81685-8_33>: the original definition.
