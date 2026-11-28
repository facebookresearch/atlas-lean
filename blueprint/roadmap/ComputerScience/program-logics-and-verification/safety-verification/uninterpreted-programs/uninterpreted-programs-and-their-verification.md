# Uninterpreted programs and their verification problem

An uninterpreted program is a while program over finitely many variables whose assignments apply uninterpreted function symbols and whose conditions compare variables. It is correct if every execution that is feasible in some data model ends in a state satisfying an equality postcondition.

**Programs.** Fix a finite set $V$ of variables and an algebraic signature $\Sigma = (\mathcal{C}, \mathcal{F})$ of constants and function symbols with arities, containing a constant $\hat{x}$ for the initial value of each $x \in V$. Programs (with relations and constants eliminated, which loses no generality) are

$$
s ::= \mathtt{skip} \mid x := y \mid x := f(\vec{z}) \mid \mathtt{assume}(c) \mid s ; s \mid \mathtt{if}\ c\ \mathtt{then}\ s\ \mathtt{else}\ s \mid \mathtt{while}\ c\ s, \qquad c ::= x = y \mid x \ne y,
$$

with $x, y \in V$, $f \in \mathcal{F}$ and $\vec{z}$ a tuple of variables.

**Executions.** Executions are words over the letters $x := y$, $x := f(\vec{z})$, $\mathtt{assume}(x = y)$, $\mathtt{assume}(x \ne y)$. The complete executions $\mathrm{Exec}(s)$ are defined by $\mathrm{Exec}(\mathtt{skip}) = \varepsilon$, a letter for each assignment and assume, concatenation for $;$, $\mathtt{assume}(c) \cdot \mathrm{Exec}(s_1) \cup \mathtt{assume}(\neg c) \cdot \mathrm{Exec}(s_2)$ for the conditional and $[\mathtt{assume}(c) \cdot \mathrm{Exec}(s)]^* \cdot \mathtt{assume}(\neg c)$ for the loop; partial executions are their prefixes. The term $\mathrm{comp}(\rho, x)$ computed for $x$ by $\rho$ is $\hat{x}$ for the empty execution, is updated by $x := y$ to $\mathrm{comp}(\rho, y)$ and by $x := f(z_1, \dots, z_r)$ to $f(\mathrm{comp}(\rho, z_1), \dots, \mathrm{comp}(\rho, z_r))$; $\mathrm{Terms}(\rho)$ is the set of terms computed along $\rho$. The equality assumes $\alpha(\rho)$ are the pairs $(\mathrm{comp}(\sigma, x), \mathrm{comp}(\sigma, y))$ for each prefix $\sigma \cdot \mathtt{assume}(x = y)$ of $\rho$, and the disequality assumes $\beta(\rho)$ are defined likewise.

**Verification problem.** A data model $\mathcal{M}$ interprets the constants and function symbols over a universe; $\rho$ is feasible in $\mathcal{M}$ if $\mathcal{M}$ equates the two terms of every pair in $\alpha(\rho)$ and distinguishes those of every pair in $\beta(\rho)$. Postconditions are formulas $\varphi ::= x = y \mid \varphi \vee \varphi \mid \neg\varphi$ over $V$. Given $s$ and $\varphi$, the verification problem asks whether for every data model $\mathcal{M}$ and every $\rho \in \mathrm{Exec}(s)$ feasible in $\mathcal{M}$, $\mathcal{M}$ satisfies $\varphi$ when each $x$ denotes the value of $\mathrm{comp}(\rho, x)$. Without loss of generality $\varphi$ is false, and the question is whether no complete execution is feasible in any data model.

**Coherence.** Write $\cong_\sigma$ for the congruence closure of $\alpha(\sigma)$ on terms. An execution $\rho$ is memoizing if for every prefix $\sigma \cdot (x := f(\vec{z}))$ of $\rho$ computing a term $t$ such that $t \cong_\sigma t'$ for some $t' \in \mathrm{Terms}(\sigma)$, there is $y \in V$ with $\mathrm{comp}(\sigma, y) \cong_\sigma t$. It has early assumes if for every prefix $\sigma \cdot \mathtt{assume}(x = y)$ and every $t' \in \mathrm{Terms}(\sigma)$ that is a superterm, modulo $\cong_\sigma$, of $\mathrm{comp}(\sigma, x)$ or of $\mathrm{comp}(\sigma, y)$, there is $z \in V$ with $\mathrm{comp}(\sigma, z) \cong_\sigma t'$. An execution is coherent if it is memoizing and has early assumes; a program is coherent (memoizing, with early assumes) if all its executions are.

## Depends on

None.

## Proof depends on

None.

## Remarks

Verifying an uninterpreted program means verifying it under every interpretation of its functions, which covers abstractions of heap updates and data-structure operations. For coherent programs the verification problem is decidable and PSPACE-complete: feasible coherent executions are recognized by a finite automaton that tracks a congruence on the current variables only. Whether a program is coherent is itself decidable.

## Sources

- Umang Mathur, P. Madhusudan and Mahesh Viswanathan, "Decidable verification of uninterpreted programs", *Proceedings of the ACM on Programming Languages* 3(POPL), 29 pages, 2019, <https://doi.org/10.1145/3290359>; read as arXiv:1811.00192v4, <https://arxiv.org/abs/1811.00192v4>: Section 2 (signatures, program syntax, executions, computed terms, assumes, feasibility and the definition of the verification problem) and Section 3 (the definitions of coherent executions and coherent programs) of that version.
