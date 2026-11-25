# Type safety of exceptions and continuations, and Griffin's correspondence

Take a call-by-value functional language with a control-stack (stack machine) dynamics, whose states are a stack $k$ with an
expression being evaluated or a value being returned, and in which a state is *final* when it returns a value to the empty stack.

- **Exceptions.** Add $\mathrm{raise}(e)$ and a handler $\mathrm{handle}\ e_1\ \mathrm{ow}\ x \Rightarrow e_2$, and count as final also a state in which an
  uncaught exception propagates through the entire stack. Then states typed by the stack typing satisfy safety: typing is preserved by
  each transition, and every well-typed state is final or can take a step.
- **Continuations.** Add the type $\tau\ \mathrm{cont}$ of reified control stacks, $\mathrm{letcc}\ x\ \mathrm{in}\ e : \tau$ when $x : \tau\ \mathrm{cont} \vdash e : \tau$, and
  $\mathrm{throw}\ e_1\ \mathrm{to}\ e_2 : \tau'$ for any $\tau'$ when $e_1 : \tau_1$ and $e_2 : \tau_1\ \mathrm{cont}$. Evaluating $\mathrm{letcc}$ binds $x$ to the current stack;
  throwing a value to a continuation discards the current stack. Again typing is preserved, and every well-typed state is final or
  steps.
- **Griffin's correspondence.** In a typed version of Idealized Scheme with a type $\bot$, $\neg \alpha = \alpha \to \bot$, and a control operator $\mathcal{C}$ with
  $\mathcal{C}(M) : \alpha$ whenever $M : \neg\neg\alpha$, typed terms correspond to natural deduction proofs in classical implicational logic, and
  every evaluation of a well-typed term is finite.

## Proof depends on

- [Progress for closed STLC terms](../operational-semantics-of-the-simply-typed-lambda/progress.md)
- [The Curry–Howard correspondence for implicational logic](the-curryhoward-correspondence-for.md)

## Sources

- R. Harper, *Practical Foundations for Programming Languages*, Cambridge University Press, 2012 (draft edition of 2012): Chapter 28 (failures, final states including uncaught failure, Theorem 28.1, and Section 28.2, where the safety theorem extends to exceptions), Chapter 29 (rules 29.1–29.6, Lemma 29.1 and Theorem 29.2) and Section 31.6 (Griffin's computational interpretation of classical logic).
- T. G. Griffin, "A formulae-as-types notion of control", *Proceedings of the 17th ACM POPL*, 1990, <http://www.cs.ru.nl/~freek/courses/tt-2011/papers/griffin.pdf>: Abstract and Sections 3 and 7 (typing of $\mathcal{C}$, the correspondence with classical implicational logic, Theorem 6 on finite evaluation).
