# Functionally recursive groups and contracting automata groups

A functionally recursive group is a finitely generated group acting on finite words, given by a transducer that says how each generator rewrites the first letter and which word in the generators acts on the rest; automata and contracting automata groups are the cases where these words do not grow or eventually shrink.

**Functionally recursive groups.** Let $A$ be a finite alphabet, $S$ a finite set and $F_S$ the free group on $S$. A map $\Phi\colon A \times S \to F_S \times A$ (an *asynchronous transducer*) defines an action of $F_S$ on the set $A^*$ of finite words over $A$: if $\Phi(a_1, s) = (g', a_1')$ then

$$
(a_1 a_2 \cdots a_n)^s = a_1' (a_2 \cdots a_n)^{g'},
$$

extended to all of $F_S$. The *group presented by $\Phi$*, written $\langle \Phi \rangle$, is the quotient of $F_S$ acting faithfully on $A^*$; a finitely generated [group](../../../group-basics/group.md) given in this way is *functionally recursive* (or self-similar).

**Automata groups.** When $\Phi$ takes the form $\Phi\colon A \times S \to S \times A$ (a *finite state transducer*), $\langle \Phi \rangle$ is an [automaton group](automaton-group.md).

**Contracting groups.** For $g \in G = \langle \Phi \rangle$ and $u \in A^*$, the state $g@u$ is the element with $(uv)^g = u^g v^{g@u}$ for all $v$. An automata group $G$ is *contracting* if there is a finite set $N \subseteq G$ such that for every $g \in G$ there is $n(g)$ with $g@u \in N$ whenever $|u| \ge n(g)$. A finite state transducer is *nuclear* when its set of states $S$ contains the minimal such set $N$ (the nucleus) and $\overline{\Phi}(A \times S^2) \subseteq S \times A$, where $\overline{\Phi}$ is the induced map on $A \times G$; nuclear transducers generate contracting groups.

## Depends on

- [Group](../../../group-basics/group.md)
- [Automaton group](automaton-group.md)

## Proof depends on

None.

## Sources

- Laurent Bartholdi and Ivan Mitrofanov, "The word and order problems for self-similar and automata groups", *Groups, Geometry, and Dynamics* 14(2):705–728, 2020, doi:[10.4171/GGD/560](https://doi.org/10.4171/GGD/560). Numbering of the version read, arXiv:1710.10109v4: Section 1 (definitions of functionally recursive groups, automata groups and contracting groups) and the definition of contracting groups and nuclear transducers in Section 3.4.
