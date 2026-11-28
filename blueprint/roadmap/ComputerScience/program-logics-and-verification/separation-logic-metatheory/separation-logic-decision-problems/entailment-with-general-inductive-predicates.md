# Entailment in separation logic with general inductive predicates is undecidable

Entailment between separation-logic assertions built from points-to atoms, separating conjunction and user-defined inductive predicates is undecidable when the predicate definitions are unrestricted.

**Assertions.** Variables are split into existential variables and fixed stack variables. Over a finite set of predicate names with arities, pure formulas are $\varphi ::= \top \mid \bot \mid x = y \mid \neg\varphi \mid \varphi \wedge \varphi$, spatial formulas are $\sigma ::= \mathsf{emp} \mid \mathsf{tt} \mid \mathsf{pt}(x, (x_1, \dots, x_m)) \mid \mathsf{pred}(y_1, \dots, y_k) \mid \sigma * \sigma \mid \alpha$, and assertions are $\alpha ::= \exists a_1 \dots a_n.\, \sigma \wedge \varphi$ ($m \ge 1$, $n \ge 0$), with $*$ commutative. A set $\mathcal{P}$ of inductive predicates gives each predicate name exactly one definition $\mathsf{pred}(a_1, \dots, a_k) := \alpha_1 \mid \cdots \mid \alpha_m$ by flat assertions without unbounded existential variables. Unraveling replaces a predicate atom by an instance of one of its disjuncts; an unraveling is complete when no predicate atom remains.

**Semantics.** An interpretation is a selector graph $I = (V, E, \ell, s)$: a set of nodes $V$, an arity $s(v) \in \mathbb{N}$ for each node (nodes of positive arity are allocated cells), selectors $E(v, i) \in V$ for $i \le s(v)$, and a finite labeling $\ell$ of fixed stack variables by nodes. $I = I_1 * I_2$ splits the allocated nodes between $I_1$ and $I_2$, keeping $V$, $\ell$ and the selectors of each allocated node. Then $I \models \mathsf{emp}$ iff no node is allocated, $\mathsf{tt}$ always holds, $I \models \mathsf{pt}(x, (x_1, \dots, x_m))$ iff exactly the node $\ell(x)$ is allocated, with arity $m$ and selectors $\ell(x_1), \dots, \ell(x_m)$, $*$ is interpreted by splitting, pure formulas by equality of labels, and existential variables by extending $\ell$. $I \models_{\mathcal{P}} \alpha$ if $I$ satisfies some complete unraveling of $\alpha$, and $\alpha \models_{\mathcal{P}} \alpha'$ if every $I$ with $I \models_{\mathcal{P}} \alpha$ satisfies $I \models_{\mathcal{P}} \alpha'$.

**Theorem.** The entailment problem (input: assertions $\alpha, \alpha'$ and a set $\mathcal{P}$ of inductive predicates; question: does $\alpha \models_{\mathcal{P}} \alpha'$ hold?) is undecidable.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

For a PCP instance $(v_1, w_1), \dots, (v_k, w_k)$ over $\{0, 1\}$ one defines predicates where $\mathsf{PCP}(x, y)$ generates all tilings, the $v$-word as a list from $x$ and the $w$-word from $y$, letters being pointers to two fixed stack variables $x_0, x_1$, and $\overline{\mathsf{PCP}}(x, y)$ generates the incorrect tilings: the empty one, those with a position where the two words differ, and those with words of different lengths. Then the instance has a solution iff $\mathsf{PCP}(x, y) \wedge x_0 \ne x_1 \not\models_{\mathcal{P}} \overline{\mathsf{PCP}}(x, y)$. The same paper shows that the fragment of Iosif, Rogalewicz and Simacek with decidable entailment is EXPTIME-hard, and a referee's remark gives undecidability of satisfiability once conjunction of spatial formulas is allowed.

## Sources

- Timos Antonopoulos, Nikos Gorogiannis, Christoph Haase, Max Kanovich and Joël Ouaknine, "Foundations for decision problems in separation logic with general inductive predicates", *Foundations of Software Science and Computation Structures (FoSSaCS 2014)*, Lecture Notes in Computer Science 8412, Springer, 411–425, 2014, <https://doi.org/10.1007/978-3-642-54830-7_27>; read as the open-access publisher version, <https://link.springer.com/content/pdf/10.1007/978-3-642-54830-7_27.pdf>: Section 2 (syntax and selector-graph semantics), Theorem 3 and its proof in Section 3, and Remark 4.
