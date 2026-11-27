# Safety automata for the general safety fragment

Let $\mathrm{AP}$ be a set of atomic propositions. The general safety fragment of LTL consists of the formulas built from propositional formulas over $\mathrm{AP}$ (evaluated at the first letter) by conjunction $\psi \wedge \rho$, disjunction $\psi \vee \rho$, next $\mathsf{X}\psi$ and always $\mathsf{G}\psi$. Words are infinite sequences of letters $s_0 s_1 s_2 \cdots$ with $s_i \subseteq \mathrm{AP}$, and an atom $p$ holds at a letter $s$ exactly when $p \in s$.

The following holds: for every formula $\psi$ of the general safety fragment there are a finite set $S$ of states and a nondeterministic Büchi automaton $A$ with state set $S$ over the alphabet $2^{\mathrm{AP}}$ such that every state of $A$ is accepting and

$$L_\omega(A) = \{\, w \in (2^{\mathrm{AP}})^{\omega} : w \models \psi \,\}.$$

Since all states are accepting, $L_\omega(A)$ is the set of words on which $A$ has an infinite run.

## Sources

- O. Kupferman and M. Y. Vardi, "Model checking of safety properties", *Formal Methods in System Design* 19 (2001), 291-314.
- S. Zhu, L. M. Tabajara, J. Li, G. Pu and M. Y. Vardi, "A Symbolic Approach to Safety LTL Synthesis", HVC 2017, [arXiv:1709.07495](https://arxiv.org/abs/1709.07495), Definitions 3 and 6 and Theorem 5 of the arXiv version.
