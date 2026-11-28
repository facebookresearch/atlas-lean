# Oblivious and semi-oblivious chase termination

In the oblivious chase every tuple-generating dependency fires once for each match of its body, and in the semi-oblivious chase once for each match of its frontier; the chase terminates on an instance when the structure it builds is finite.

**Programs.** A *tuple-generating dependency* (TGD) is a rule

$$
\Phi(\bar x, \bar y) \Rightarrow \exists \bar z\ \Psi(\bar x, \bar z),
$$

where $\Phi$ and $\Psi$ are conjunctions of relational atoms without equality over a relational signature $\Sigma$, and $\bar x, \bar y, \bar z$ are tuples of variables ($\bar z$ may be empty, giving a plain Datalog rule). It is *single-head* if $\Psi$ is a single atom. A *program* $\mathcal T$ is a finite set of TGDs; the signature is *ternary* if every relation symbol has arity at most $3$. A database instance $D$ is a finite $\Sigma$-structure.

**Oblivious chase.** Replace each TGD $(i)\ \Phi(\bar x, \bar y) \Rightarrow \exists \bar z\, \Psi(\bar x, \bar z)$ of $\mathcal T$ by the Skolemized rule $\Phi(\bar x, \bar y) \Rightarrow \Psi(\bar x, \bar h_i(\bar x, \bar y))$, with a fresh Skolem function symbol per existential variable, depending on all universally quantified variables of the rule. $\mathrm{Chase}(D, \mathcal T)$ is the least Herbrand model of the Skolemized program over the elements of $D$ taken as constants. Thus one new tuple of witnesses is created for each tuple $\bar a, \bar b$ satisfying $\Phi$, whether or not a witness already exists.

**Semi-oblivious chase.** The same with Skolem terms depending only on the frontier $\bar x$: one tuple of witnesses for each $\bar a$ such that $\exists \bar y\, \Phi(\bar a, \bar y)$ holds.

**Termination.** For either variant, the $\mathcal T$-chase *terminates on* $D$ if $\mathrm{Chase}(D, \mathcal T)$ is finite, equivalently if its terms have bounded depth. The order in which matches are processed does not affect the result, provided every match is eventually processed. The *all-instances termination problem* asks, for a given program $\mathcal T$, whether the $\mathcal T$-chase terminates on every finite database instance $D$.

Both variants are eager, in contrast with the [standard (restricted) chase](restricted-chase-sequences.md), which adds witnesses only for matches whose head is not yet satisfied and therefore depends on the order of steps. In terms of triggers (pairs of a TGD and a match of its body), the oblivious chase applies every trigger exactly once and the semi-oblivious chase one trigger for each match of the frontier, whether or not the head is already satisfied; the Skolemized programs above compute the same result. An element $a_\Sigma$ of $D$ is a *well of positivity* if $R(a_\Sigma, \dots, a_\Sigma)$ holds for every $R \in \Sigma$; let $D_\Sigma$ be the one-element instance whose element is a well of positivity. Marnette's critical-instance lemma states that the oblivious $\mathcal T$-chase terminates on every instance if and only if it terminates on $D_\Sigma$: a derivation of a deep term from any $D$ becomes, after identifying all elements of $D$ with $a_\Sigma$, a derivation of a term of the same depth from $D_\Sigma$. Consequently all-instances termination of the oblivious and semi-oblivious chase is recursively enumerable.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](../../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Least Herbrand model](../../../programming-language-semantics/effects-modules-and-logic-programming/least-model.md)

## Proof depends on

None.


## Sources

- Tomasz Gogacz and Jerzy Marcinkowski, "All-Instances Termination of Chase is Undecidable", in *Automata, Languages, and Programming (ICALP 2014), Part II*, Lecture Notes in Computer Science 8573, Springer, 2014, pp. 293–304, <https://doi.org/10.1007/978-3-662-43951-7_25>; read as arXiv:1401.4840v2, <https://arxiv.org/abs/1401.4840v2>: Section 1 and Section 3.1 ("The well of positivity", with Lemma 3 on the critical instance), in the numbering of that version.
