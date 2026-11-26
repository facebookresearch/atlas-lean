# Functions definable in System T

Write $\to_T$ for one-step reduction of [Gödel's System T](godel-s-system-t.md) in its presentation with the constants $0$, $\mathrm{S}$ and $\mathrm{R}_A$: β-reduction together with the recursor rules $\mathrm{R}\,u\,v\,0 \to u$ and $\mathrm{R}\,u\,v\,(\mathrm{S}\,t) \to v\,t\,(\mathrm{R}\,u\,v\,t)$, in any context; $=_T$ for the convertibility it generates; and $\underline{n} = \mathrm{S}^n\,0$ for the numerals. A total function $f : \mathbb{N}^k \to \mathbb{N}$ is *definable in System T* if there is a closed term $F$ with
$\vdash F : \mathrm{nat} \to \cdots \to \mathrm{nat} \to \mathrm{nat}$ ($k$ arguments) such that

$$F\, \underline{m_1} \cdots \underline{m_k} =_T \underline{f(m_1, \dots, m_k)} \quad\text{for all } m_1, \dots, m_k \in \mathbb{N}.$$

Addition, multiplication, exponentiation and the predecessor are definable, every primitive recursive function is definable, and with recursion at
higher types so is the Ackermann function. Since terms of type $\mathrm{nat} \to \mathrm{nat}$ can be enumerated and each defines a total function, a
diagonal argument gives a total recursive function that is not definable in System T.

## Depends on

- [Gödel's System T](godel-s-system-t.md)

## Proof depends on

- [Strong normalization of System T](strong-normalization-of-system-t.md)
- [Closed normal forms of System T](closed-normal-forms-of-system-t.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Example 11.6.7, Definition 11.6.8 and the remarks after Remark 11.6.9 (primitive recursive functions are definable; the diagonal argument).
