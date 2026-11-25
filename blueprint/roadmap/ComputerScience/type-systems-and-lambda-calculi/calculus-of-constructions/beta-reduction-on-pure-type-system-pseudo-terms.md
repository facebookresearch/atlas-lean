# Beta reduction on pure type system pseudo-terms is confluent

Fix a set of sorts $\mathcal{S}$. The *pseudo-terms* of a pure type system are

$$
T ::= x \mid s \mid T\, T \mid \lambda x{:}T.\, T \mid \Pi x{:}T.\, T \qquad (s \in \mathcal{S}),
$$

taken up to $\alpha$-conversion. $\beta$-reduction $\to_\beta$ is the compatible closure of $(\lambda x{:}A.\, M)\, N \to M[x := N]$, with reflexive-transitive closure $\twoheadrightarrow_\beta$ and $\beta$-conversion $=_\beta$. Reduction is defined on all pseudo-terms, typable or not.

**Theorem.**
1. **Church–Rosser.** If $M \twoheadrightarrow_\beta N_1$ and $M \twoheadrightarrow_\beta N_2$, then $N_1 \twoheadrightarrow_\beta N_3$ and $N_2 \twoheadrightarrow_\beta N_3$ for some $N_3$. Hence $M =_\beta N$ iff $M$ and $N$ have a common reduct.
2. **Injectivity of $\Pi$.** If $\Pi x{:}A.\, B =_\beta \Pi x{:}A'.\, B'$, then $A =_\beta A'$ and $B =_\beta B'$.
3. Distinct sorts are not convertible, and a sort is not convertible to a $\Pi$-type.

**Proof.**
1. Use *parallel reduction* $\Rightarrow$, which reduces any set of redexes present in a term simultaneously. It is reflexive, compatible with all constructors, including the type annotation in $\lambda x{:}A$ and both parts of $\Pi x{:}A.\, B$, and satisfies $M \Rightarrow M'$, $N \Rightarrow N'$ $\Longrightarrow$ $M[x := N] \Rightarrow M'[x := N']$. It has the diamond property. Let $M^\ast$ be the *complete development* of $M$, which contracts all redexes of $M$ from the inside out. By induction on $M$, $M \Rightarrow N$ implies $N \Rightarrow M^\ast$, so any two parallel reducts of $M$ join at $M^\ast$. Since ${\to_\beta} \subseteq {\Rightarrow} \subseteq {\twoheadrightarrow_\beta}$, $\twoheadrightarrow_\beta$ inherits the diamond property. The root contraction of $(\lambda x{:}A.\, M)\, N$ discards the annotation $A$, but $\beta$-reduction may still take place inside annotations, since it is the compatible closure; parallel reduction and the complete development reduce inside $A$ like any other subterm, so the untyped proof goes through with one more structural case for the annotation of each binder.
2. By part 1, both sides reduce to a common term. Every reduct of $\Pi x{:}A.\, B$ is of the form $\Pi x{:}A_1.\, B_1$ with $A \twoheadrightarrow_\beta A_1$ and $B \twoheadrightarrow_\beta B_1$, because no redex has a $\Pi$ at its root. Comparing components gives the claim.
3. Sorts are normal forms, and reducts of a $\Pi$-type are $\Pi$-types.

## Sources

- H. Barendregt and E. Barendsen, *Introduction to Lambda Calculus*, revised edition, 2000, <https://www.cse.chalmers.se/research/group/logic/TypesSS05/Extra/geuvers.pdf>, Chapter 4: the Church–Rosser theorem for $\beta$-reduction (4.9), its corollaries (4.11), and the proof plan of 4.13–4.19 through the strip lemma.
- H. Geuvers, *Introduction to Type Theory*, lecture notes, Radboud University Nijmegen, <https://www.cs.ru.nl/~herman/PUBS/IntroTT-improved.pdf>: Definition 36 (pseudo-terms with $\lambda x{:}T.T$ and $\Pi x{:}T.T$), and the remark that type checking must decide $\beta$-reduction and $\beta$-equality on pseudo-terms, using that the system is strongly normalizing and Church–Rosser.

    The extension of the untyped proof to typed binders is written out here.
- H. P. Barendregt, "Lambda calculi with types", in *Handbook of Logic in Computer Science*, vol. 2, Oxford University Press, 1992, Section 5.2 (not legible in the copy opened).
