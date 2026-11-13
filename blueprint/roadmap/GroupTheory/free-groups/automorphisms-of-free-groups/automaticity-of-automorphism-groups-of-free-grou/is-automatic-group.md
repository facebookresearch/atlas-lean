# Automatic group

A group $G$ is automatic if there are a finite alphabet $A$, an
involution $\iota$ of $A$, a map $\mathrm{ev} \colon A \to G$ with
$\mathrm{ev}(\iota(a)) = \mathrm{ev}(a)^{-1}$ for all $a \in A$, a language $L$ of words over $A$
that is exactly the set of words accepted by some deterministic finite automaton, and a natural
number $k$ with the following properties. Write $\overline{w} \in G$ for the product of the
images under $\mathrm{ev}$ of the letters of a word $w$, and $w(t)$ for the prefix of $w$ of
length $t$ (all of $w$ if $t$ exceeds its length). Every element of $G$ equals $\overline{w}$ for
some $w \in L$. For all $u, v \in L$ such that $\overline{u} = \overline{v}$, or
$\overline{u}\,\mathrm{ev}(a) = \overline{v}$ for some letter $a$, and for every $t \in \mathbb{N}$,
the element $\overline{u(t)}^{-1}\,\overline{v(t)}$ equals $\overline{w}$ for some word $w$ of
length at most $k$.

This is the fellow-traveller characterization of automatic groups (Epstein et al., Word
Processing in Groups, Theorem 2.3.5).

## Sources

- Question 7.3 [AMR-109-0302], Farb - Problems on Mapping Class Groups and Related Topics, PDF p. 339, https://www.math.uchicago.edu/~farb/papers/mcgbook.pdf.
