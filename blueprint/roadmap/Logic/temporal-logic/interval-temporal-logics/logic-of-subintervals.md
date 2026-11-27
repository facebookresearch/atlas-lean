# Logic of subintervals

The logic of subintervals is the fragment of Halpern and Shoham's modal logic of time intervals whose only modality is ⟨D⟩, "during": ⟨D⟩φ holds on an interval if φ holds on some proper subinterval.

**Definition.** Let $(D, \le)$ be a linear order. An *interval* over $D$ is a pair $[a, b]$ with $a, b \in D$ and $a \le b$; $I(D)$ is the set of all intervals. For a finite set $\mathrm{Var}$ of propositional variables, a *labeling* is a function $\gamma : I(D) \to \mathcal P(\mathrm{Var})$, and $M = (I(D), \gamma)$ is a *model*. Formulas are

$$
\varphi ::= v \mid \neg\varphi \mid \varphi \wedge \varphi \mid \langle D\rangle\varphi \qquad (v \in \mathrm{Var}),
$$

with $M, [a, b] \models v$ iff $v \in \gamma([a, b])$, Boolean connectives as usual, and $M, [a, b] \models \langle D\rangle\varphi$ iff $M, [a', b'] \models \varphi$ for some interval $[a', b'] \neq [a, b]$ with $a \le a'$ and $b' \le b$. A formula is *satisfiable in a class* $\mathcal D$ of orders if $M, [a, b] \models \varphi$ for some $(D, \le) \in \mathcal D$, some labeling $\gamma$ of $I(D)$ and some initial interval $[a, b]$. An order is *discrete* if every point with a successor (predecessor) has an immediate one: for all $a < b$ there are $a', b'$ with $a < a'$, $b' < b$ and nothing strictly between $a$ and $a'$ or between $b'$ and $b$.

Halpern–Shoham logic has one modality for each of Allen's relations between intervals (after, begins, ends, during, overlaps, later, and their inverses); the logic of subintervals keeps only $\langle D\rangle$, with $[D]\varphi = \neg\langle D\rangle\neg\varphi$. Over dense orders its satisfiability problem is decidable, as is satisfiability of the reflexive variant (where $[a', b'] = [a, b]$ is allowed) over discrete orders.

## Depends on

None.

## Proof depends on

None.

## Expansion

Since $\langle D\rangle$ looks only inside the current interval, the truth of a formula on $[a, b]$ depends only on the labeling of the subintervals of $[a, b]$; over finite orders the intervals form a directed acyclic graph in which $[a, b]$ with $a < b$ has the two immediate subintervals $[a + 1, b]$ and $[a, b - 1]$, leveled by length. Intervals $[a, a]$ of length $0$ have no proper subintervals.

## Sources

- J. Marcinkowski and J. Michaliszyn, "The Ultimate Undecidability Result for the Halpern–Shoham Logic", in *2011 IEEE 26th Annual Symposium on Logic in Computer Science (LICS 2011)*, IEEE, 2011, pp. 377–386, <https://doi.org/10.1109/LICS.2011.21>; read as arXiv:1010.4529v1 ("The Last Paper on the Halpern–Shoham Interval Temporal Logic"), <https://arxiv.org/abs/1010.4529v1>: Section 1 (Preliminaries: intervals, labelings, the semantics of $\langle D\rangle$, satisfiability in a class of orders, discreteness) and the introduction.
- J. Y. Halpern and Y. Shoham, "A propositional modal logic of time intervals", *Journal of the ACM* 38(4):935–962, 1991, <https://doi.org/10.1145/115234.115351>: Halpern–Shoham logic, as recalled in the introduction of the version of the first source read.
