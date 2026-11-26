# Prime filters of a Heyting algebra

A *filter* in a [Heyting algebra](heyting-algebra-semantics-of-ipc.md) $H$ is a nonempty subset $F \subseteq H$ such that $a \cap b \in F$ whenever $a, b \in F$, and $b \in F$ whenever $a \in F$ and $a \le b$. A filter is *proper* if $F \ne H$, equivalently $0 \notin F$, and a proper filter is *prime* if $a \cup b \in F$ implies $a \in F$ or $b \in F$.

## Depends on

- [Heyting algebra semantics of intuitionistic propositional logic](heyting-algebra-semantics-of-ipc.md)

## Sources

- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, 1998 (published as volume 149 of *Studies in Logic and the Foundations of Mathematics*, Elsevier, 2006), Section 2.5: Definition 2.5.3.
