# Type soundness of Featherweight Java

Featherweight Java (FJ) is a core calculus for Java. A program is a class table together with an expression. Expressions are variables, field accesses $e.f$, method invocations $e.m(\bar e)$, object creations $\mathbf{new}\ C(\bar e)$ and casts $(C)\,e$. Subtyping $<:$ is the reflexive and transitive closure of the subclass relation. Reduction is the nondeterministic small-step relation given by field projection, method invocation by method body lookup, and casts $(D)\,\mathbf{new}\ C(\bar v) \to \mathbf{new}\ C(\bar v)$ when $C <: D$, closed under congruence. Values are the expressions $v ::= \mathbf{new}\ C(\bar v)$. Let the class table be well formed.

1. **Subject reduction.** If $\Gamma \vdash e : C$ and $e \to e'$, then $\Gamma \vdash e' : C'$ for some $C' <: C$.
2. **Progress.** Let $e$ be well typed. If $e$ contains $\mathbf{new}\ C_0(\bar e).f$, then $f$ is among the fields of $C_0$. If $e$ contains $\mathbf{new}\ C_0(\bar e).m(\bar d)$, then the body of $m$ in $C_0$ is defined and takes as many parameters as there are arguments in $\bar d$.
3. **Type soundness.** If $\emptyset \vdash e : C$ and $e \to^* e'$ with $e'$ a normal form, then $e'$ is either a value $v$ with $\emptyset \vdash v : D$ for some $D <: C$, or an expression containing a failed downcast $(D)\,\mathbf{new}\ C(\bar e)$ with $C \not<: D$.
4. **Cast-safe programs.** If the typing derivations use no downcasts and no "stupid" casts between unrelated classes, then reduction preserves this property, and every normal form reached from such an expression is a value.

Subject reduction can turn a downcast into a stupid cast. For this reason the typing rules include a stupid-cast rule, which only signals a warning.

## Sources

- A. Igarashi, B. C. Pierce and P. Wadler, "Featherweight Java: a minimal core calculus for Java and GJ", *ACM Transactions on Programming Languages and Systems* 23(3):396–450, 2001, <https://www.cis.upenn.edu/~bcpierce/papers/fj-toplas.pdf>, Section 2: Fig. 3 (reduction rules), Theorem 2.4.1 (subject reduction), Theorem 2.4.2 (progress), Theorem 2.4.3 (type soundness), Theorems 2.4.4 and 2.4.5 and Corollary 2.4.6 (cast-safe programs).
