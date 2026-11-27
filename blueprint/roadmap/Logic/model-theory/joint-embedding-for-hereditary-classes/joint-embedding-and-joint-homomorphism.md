# Joint embedding and joint homomorphism properties

A class of finite structures has the joint embedding property if any two of its members embed into a common member, and the joint homomorphism property if any two map homomorphically into a common member; for hereditary classes the first is the same as being atomic.

**Definition.** A class $\mathcal C$ of finite structures in a relational language is *hereditary* if it is closed under isomorphism and under induced substructures. For a set $\mathcal F$ of finite structures, the class $\mathrm{Forb}(\mathcal F)$ of finite structures with no induced substructure isomorphic to a member of $\mathcal F$ is hereditary, and every hereditary class has this form; for graphs, $\mathcal F$ is a set of *forbidden induced subgraphs*. The class $\mathcal C$ has the

- *joint embedding property* (JEP) if for all $A, B \in \mathcal C$ there is $C \in \mathcal C$ into which both $A$ and $B$ embed (as induced substructures);
- *joint homomorphism property* (JHP) if for all $A, B \in \mathcal C$ there is $C \in \mathcal C$ admitting homomorphisms from $A$ and from $B$.

A hereditary class has the JEP iff it is *atomic*, that is, not the union of two proper hereditary subclasses. For a class specified by forbidden substructures, the JEP is also equivalent to the existence of a countable structure avoiding the forbidden substructures into which every member of the class embeds.

## Depends on

None.

## Proof depends on

None.

## Expansion

For a hereditary class of finite structures in a finite relational language, failure of the JEP is recursively enumerable: if $A$ and $B$ embed jointly into some $C \in \mathcal C$, then they embed jointly into the induced substructure of $C$ on the union of the two images, which lies in $\mathcal C$ and has at most $|A| + |B|$ elements, so it suffices to search finitely many candidates for each pair. Unlike the JEP, the JHP is not preserved under changing to a quantifier-free interdefinable language. The JHP is of interest for infinite-domain constraint satisfaction problems (Bodirsky).

## Sources

- S. Braunfeld, "The undecidability of joint embedding and joint homomorphism for hereditary graph classes", *Discrete Mathematics & Theoretical Computer Science* 21(2), Permutation Patterns 2018, 2019, paper 9, <https://doi.org/10.23638/DMTCS-21-2-9>; numbers from arXiv:1903.11932v4, <https://arxiv.org/abs/1903.11932v4>: Section 1 (definitions and the equivalence with atomicity and universal objects), Section 2 (co-recursive enumerability of the JEP) and Section 5 (the joint homomorphism property).
