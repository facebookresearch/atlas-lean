# Separation algebras

A *separation algebra* is a cancellative partial commutative monoid $(\Sigma, \bullet, u)$: $\bullet$ is a partial binary operation on $\Sigma$ for which the unit, commutativity and associativity laws hold in the sense that both sides are defined and equal or both are undefined, and for each $\sigma \in \Sigma$ the partial function $\sigma \bullet (\cdot)$ is injective. States $\sigma_0, \sigma_1$ are *separate*, $\sigma_0 \# \sigma_1$, if $\sigma_0 \bullet \sigma_1$ is defined, and $\sigma_0$ is a *substate* of $\sigma_2$, $\sigma_0 \preceq \sigma_2$, if $\sigma_2 = \sigma_0 \bullet \sigma_1$ for some $\sigma_1$. *Predicates* over $\Sigma$ are the subsets of $\Sigma$; they form an ordered total commutative monoid under

$$p \ast q = \{\sigma_0 \bullet \sigma_1 : \sigma_0 \# \sigma_1,\ \sigma_0 \in p,\ \sigma_1 \in q\}, \qquad \mathrm{emp} = \{u\},$$

in which $p \ast (\cdot)$ preserves all unions. Examples are heaps, the finite partial functions from l-values to r-values with union of functions with disjoint domains; heaps with permissions drawn from a permission algebra such as the fractions in $(0, 1]$; stores and heaps together (variables as resource); and multisets of places of a Petri net with multiset union.

## Sources

- C. Calcagno, P. W. O'Hearn and H. Yang, "Local action and abstract separation logic", *Proceedings of the 22nd Annual IEEE Symposium on Logic in Computer Science (LICS 2007)*, IEEE, 2007, pp. 366–378, <https://doi.org/10.1109/LICS.2007.30>, author copy <https://www.cs.ox.ac.uk/people/hongseok.yang/paper/asl-short.pdf>, Section 2, Definitions 1 and 2 and the examples after Definition 1.
