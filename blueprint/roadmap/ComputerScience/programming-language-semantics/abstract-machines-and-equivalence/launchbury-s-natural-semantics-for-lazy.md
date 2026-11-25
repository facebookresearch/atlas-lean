# Launchbury's natural semantics for lazy evaluation

**Normalized terms.** The language is the untyped lambda calculus with recursive let,

$$e ::= \lambda x.\, e \mid e\,x \mid x \mid \mathrm{let}\ x_1 = e_1, \dots, x_n = e_n\ \mathrm{in}\ e,$$

in normalized form: every application has a variable as its argument, and all bound variables are distinct. An arbitrary term is normalized by renaming all bound variables to fresh ones and by replacing each application $e_1 e_2$ whose argument is not a variable with $\mathrm{let}\ y = e_2\ \mathrm{in}\ e_1\,y$, with $y$ fresh.

**Heaps and values.** A heap $\Gamma$ is a partial function from variables to terms, a set of bindings $x \mapsto e$ with distinct variables. A value is a term in weak head normal form, that is, a lambda abstraction.

**Judgments.** $\Gamma : e \Downarrow \Delta : z$ means that $e$, evaluated in heap $\Gamma$, reduces to the value $z$ with final heap $\Delta$. The rules are:

- **Lambda.** $\Gamma : \lambda x.\, e \Downarrow \Gamma : \lambda x.\, e$.
- **Application.** If $\Gamma : e \Downarrow \Delta : \lambda y.\, e'$ and $\Delta : e'[x/y] \Downarrow \Theta : z$, then $\Gamma : e\,x \Downarrow \Theta : z$.
- **Variable.** If $\Gamma : e \Downarrow \Delta : z$, then $(\Gamma, x \mapsto e) : x \Downarrow (\Delta, x \mapsto z) : \hat z$, where $\hat z$ is $z$ with all bound variables renamed to fresh ones.
- **Let.** If $(\Gamma, x_1 \mapsto e_1, \dots, x_n \mapsto e_n) : e \Downarrow \Delta : z$, then $\Gamma : \mathrm{let}\ x_1 = e_1, \dots, x_n = e_n\ \mathrm{in}\ e \Downarrow \Delta : z$.

The variable rule evaluates the bound term in the heap without the binding for $x$, then rebinds $x$ to the resulting value, so the work is shared by later uses of $x$. A missing binding for $x$ during its own evaluation, a "black hole", leaves no rule applicable. Substituting a variable in the application rule duplicates no work.

## Sources

- J. Launchbury, "A natural semantics for lazy evaluation", *Proceedings of the 20th ACM Symposium on Principles of Programming Languages (POPL)*, 1993, pp. 144–154: Section 3.1 (normalized terms and the normalizing transformation), Section 3.2 and Figure 1 (heaps, values in weak head normal form, and the Lambda, Application, Variable and Let rules).
