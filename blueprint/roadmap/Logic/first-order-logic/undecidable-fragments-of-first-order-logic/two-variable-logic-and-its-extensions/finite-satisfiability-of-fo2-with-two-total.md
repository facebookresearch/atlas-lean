# Finite satisfiability of FO² with two total preorders is undecidable

Two-variable logic over finite structures with two total preorders and arbitrary unary relations has an undecidable finite satisfiability problem, and so does two-variable logic with two linear orders and one total preorder.

**Theorem (Schwentick and Zeume).** Consider [two-variable logic](two-variable-logic-and-its-counting-extension.md) FO² with equality over finite structures that interpret the distinguished binary symbols as indicated and carry any number of additional unary relations, but no other binary relations. Then finite satisfiability is undecidable

1. for $\mathrm{FO}^2(\precsim_1, \precsim_2)$, two total preorders; and
2. for $\mathrm{FO}^2(\leq_1, \leq_2, \precsim_3)$, two linear orders and one total preorder.

By contrast, the source shows that finite satisfiability of $\mathrm{FO}^2(\leq_1, \precsim_2)$, one linear order and one total preorder, is EXPSPACE-complete, and that with two linear orders and no total preorder it is in EXPSPACE; so it is the second total preorder, or a third order, that causes undecidability. Since a total preorder encodes an equivalence relation, these results sit next to the undecidability of FO² with three equivalence relations (Kieroński and Otto).

## Depends on

- [Two-variable logic and its counting extension](two-variable-logic-and-its-counting-extension.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

Both clauses are proved by reductions from the Post correspondence problem over the alphabet $\{0, 1\}$. Finite structures with total preorders are viewed as finite sets of labeled points in the plane, each preorder comparing one coordinate. For an instance $(u_1, v_1), \dots, (u_k, v_k)$ a solution is encoded as a point set in which the letters of $u_{i_1} \cdots u_{i_m}$ and of $v_{i_1} \cdots v_{i_m}$ are matched position by position through the two preorders, and a two-variable sentence $\varphi_I$ checks locally that the encoding is consistent, so that $\varphi_I$ has a finite model iff the instance has a solution. For clause 2 one total preorder is simulated by two linear orders in the same scheme.

## Sources

- T. Schwentick and T. Zeume, "Two-variable logic with two order relations", *Logical Methods in Computer Science* 8(1), Paper 15, 2012, doi:10.2168/LMCS-8(1:15)2012; read as arXiv:1110.1439v3, <https://arxiv.org/abs/1110.1439v3>: the two theorems of the subsection "Undecidable Extensions" of arXiv:1110.1439v3 (finite satisfiability of $\mathrm{FO}^2(\precsim_1, \precsim_2)$ and of $\mathrm{FO}^2(\leq_1, \leq_2, \precsim_3)$ is undecidable) and their proofs.
