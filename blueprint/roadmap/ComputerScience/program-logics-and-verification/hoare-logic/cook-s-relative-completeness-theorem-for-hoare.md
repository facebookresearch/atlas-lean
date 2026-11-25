# Cook's relative completeness theorem for Hoare logic

Let $\mathcal{L}$ be a first-order assertion language with an interpretation $\mathcal{I}$, and consider while programs whose expressions are
terms and quantifier-free formulas of $\mathcal{L}$. A formula $P\{A\}Q$ with $P, Q \in \mathcal{L}$ is *true* in $\mathcal{I}$ if every terminating
execution of $A$ from a state satisfying $P$ ends in a state satisfying $Q$. Let $\mathcal{T}$ be a proof system for $\mathcal{L}$ that is
*semantically complete* relative to $\mathcal{I}$: a formula is provable in $\mathcal{T}$ exactly when its universal closure is true in $\mathcal{I}$. Hoare
logic over $\mathcal{T}$ has the axiom $Q^e_x\{x := e\}Q$, the rules for sequencing, conditionals and $\mathbf{while}$ with an invariant, and
the rule of consequence, whose implications between assertions are discharged in $\mathcal{T}$.

**Theorem.** If $\mathcal{L}$ is expressive relative to $\mathcal{I}$ (every post relation of an assertion and a program is definable in $\mathcal{L}$), then
every formula $P\{A\}Q$ true in $\mathcal{I}$ is derivable in Hoare logic over $\mathcal{T}$. In particular, for the language of arithmetic $\mathcal{N}$
with its standard interpretation in $\mathbb{Z}$ and a complete, necessarily non-axiomatizable, proof system $\mathcal{T}$, a formula is derivable
exactly when it is true.

No axiomatizable $\mathcal{T}$ gives completeness for $\mathcal{N}$: derivable formulas are recursively enumerable, but
$\mathrm{true}\{A\}\mathrm{false}$ is true exactly when $A$ halts from no initial state.

## Proof depends on

- [First-order arithmetic is expressive for while programs](first-order-arithmetic-is-expressive-for-while.md)

## Sources

- S. A. Cook, "Soundness and completeness of an axiom system for program verification", *SIAM Journal on Computing* 7(1):70–90, 1978, <http://www.cs.utoronto.ca/~sacook/homepage/soundness.pdf>: Section 6 (Theorem 2, the definition of semantic completeness, Theorem 3 and its corollary). Cook's language also has blocks and non-recursive procedures with their rules; this page states the while-program fragment.
