# Joint embedding property

A class of structures has the joint embedding property if any two of its members embed into a common member.

**Definition.** Let $L$ be a first-order language and $K$ a class of $L$-structures. The class $K$ has the *joint embedding property* (JEP) if for all $M, N \in K$ there is $P \in K$ such that both $M$ and $N$ embed into $P$, that is, $K$ is directed under the relation "embeds into". An embedding of $L$-structures is an injective map that preserves and reflects every relation and commutes with the function symbols; in a relational language it is an isomorphism onto an induced substructure. For a class of finite structures in a relational language this is the joint embedding property of the source: any two members embed, as induced substructures, into a common member.

## Sources

- S. Braunfeld, "The undecidability of joint embedding and joint homomorphism for hereditary graph classes", *Discrete Mathematics & Theoretical Computer Science* 21(2), Permutation Patterns 2018, 2019, paper 9, <https://doi.org/10.23638/DMTCS-21-2-9>; numbers from arXiv:1903.11932v4, <https://arxiv.org/abs/1903.11932v4>: Section 1 (the definition).
- Mathlib, `FirstOrder.Language.JointEmbedding` in `Mathlib/ModelTheory/Fraisse.lean`.
