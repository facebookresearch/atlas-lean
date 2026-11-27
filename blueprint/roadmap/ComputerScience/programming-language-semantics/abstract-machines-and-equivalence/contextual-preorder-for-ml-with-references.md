# Contextual preorder for ML with references

For programs $e_1, e_2 \in \mathrm{Prog}_{ty}$ of [the ML fragment](an-ml-fragment-with-integer-references.md), write $s, e \Downarrow$ if $s, e \Rightarrow v, s'$ for some $v$ and $s'$ (so that $\mathrm{loc}(e) \subseteq \mathrm{dom}(s)$), and define

$$e_1 \le_{ctx} e_2 : ty \iff \forall x, e, ty', s.\ (x : ty \vdash e : ty') \wedge \mathrm{loc}(e[e_1/x]) \cup \mathrm{loc}(e[e_2/x]) \subseteq \mathrm{dom}(s) \wedge (s, e[e_1/x] \Downarrow) \Rightarrow (s, e[e_2/x] \Downarrow),$$

so that both plugged programs are admissible in the same initial state (a condition left implicit in the source, whose termination predicate
is defined only on such states); without this, the empty state would distinguish $()$ from $\mathrm{let}\ y = \ell\ \mathrm{in}\ ()$,
which in any state defined at $\ell$ both evaluate to $()$ without changing the state. Let $e_1 =_{ctx} e_2 : ty$ if $e_1 \le_{ctx} e_2 : ty$ and $e_2 \le_{ctx} e_1 : ty$. The program $e[-/x]$ plays the role of a context with a hole; observing termination alone, rather
than printed results, gives the same equivalence. For example, a counter object whose local reference counts up and one whose local reference counts down, each
exposing only its increment-and-read function with the sign adjusted, are contextually equivalent.

## Depends on

- [An ML fragment with integer references](an-ml-fragment-with-integer-references.md)

## Sources

- A. M. Pitts, "Operational semantics and program equivalence", in G. Barthe, P. Dybjer, L. Pinto and J. Saraiva (eds.), *Applied Semantics*, LNCS 2395, Springer, 2002, 378–412, <https://doi.org/10.1007/3-540-45699-6_8>: Section 2 (the examples $p$ and $m$), Section 3, the observation function (6) with the remark referring to Exercise B.3, Definition 3.1 and Remark 3.2.
