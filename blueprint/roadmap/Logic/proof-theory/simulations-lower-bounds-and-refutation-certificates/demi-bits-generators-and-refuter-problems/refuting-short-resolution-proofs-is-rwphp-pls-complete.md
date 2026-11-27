# Refuting short resolution proofs is complete for $\mathrm{rwPHP}(\mathsf{PLS})$

Finding an invalid step in a purported resolution refutation that is shorter than a true size lower bound is hard for the class $\mathrm{rwPHP}(\mathsf{PLS})$ for every hard formula, and for the pigeonhole principle it is complete. Hence $T^1_2+\mathrm{dwPHP}(\mathsf{PV})$ captures the reasoning needed for resolution size lower bounds.

**The class $\mathrm{rwPHP}(\mathsf{PLS})$.** An instance of $\mathrm{Iter}$ is a function $S:[L]\to[L]$; a solution is $x\in[L]$ with $x=0$ and $S(0)=0$, or $S(x)<x$, or $S(x)>x$ and $S(S(x))=S(x)$. $\mathsf{PLS}$ is the class of decision-tree total search problems with a polylogarithmic-depth decision-tree reduction to $\mathrm{Iter}$. An instance of $\mathrm{rwPHP}(\mathsf{PLS})$ with $M\le N/2$ consists of a purported surjection $f:[M]\to[N]$ and, for each $y\in[N]$, an $\mathrm{Iter}$ instance $I_y=(L,S_y)$ together with a map $g_y:[L]\to[M]$ on its solutions; a solution is a pair $(y,ans)$ with $y\in[N]$, $ans$ a solution of $I_y$, and $f(g_y(ans))\ne y$. Totality is the retraction weak pigeonhole principle applied to $y\mapsto g_y(ans(y))$.

**Theorem.** Let $\mathrm{Refuter}(s(F\vdash_{\mathrm{Res}}\bot)\le s_F)$ be the refuter problem for the resolution size lower bound $s_F$, and let $\mathrm{PHP}_{(n+1)\to n}$ be the pigeonhole principle CNF for $n+1$ pigeons and $n$ holes.

1. (Hardness for every formula.) There is a universal constant $C\ge 2$ such that the following holds. Let $L,M\ge 1$ be the parameters of $\mathrm{rwPHP}(\mathsf{PLS})$ instances and $n\ge 1$. For every unsatisfiable CNF $F$ over $n$ variables and every $s_F\ge C\cdot(nLM+|F|)$ such that every resolution refutation of $F$ requires more than $s_F$ clauses, there is a decision-tree reduction of block-depth $O(n)$ from an $\mathrm{rwPHP}(\mathsf{PLS})$ instance to a $\mathrm{Refuter}(s(F\vdash_{\mathrm{Res}}\bot)\le s_F)$ instance.
2. (Upper bound for the pigeonhole principle.) There is a uniform decision-tree reduction of block-depth 3 from the refuter problem for the bound $1.01^n$ on resolution refutations of $\mathrm{PHP}_{(n+1)\to n}$ to $\mathrm{rwPHP}(\mathsf{PLS})$: from a purported refutation with $L\le 1.01^n$ clauses it computes an $\mathrm{rwPHP}(\mathsf{PLS})$ instance, and from any solution of that instance an invalid derivation can be computed in $\mathrm{poly}(n)$ time.
3. (Completeness.) $\mathrm{Refuter}(s(\mathrm{PHP}_{(n+1)\to n}\vdash_{\mathrm{Res}}\bot)\le 1.01^n)$ is complete for $\mathrm{rwPHP}(\mathsf{PLS})$.

**Bounded-arithmetic form.** $T^1_2=\mathrm{BASIC}+\Sigma^b_1\text{-}\mathrm{IND}$, and $\mathrm{dwPHP}(\mathsf{PV})$ is the schema $\forall a>1\,\exists v<a^2\,\forall u<a\;f(u)\ne v$ for every $\mathsf{PV}$ function $f$ with parameters; the relativized theories add a unary predicate $\alpha$ encoding an exponentially long input. Let $\mathrm{LB}^{\mathrm{Res}}_{\mathrm{PHP}}(\mathsf{PV}(\alpha))$ be the $\forall\Sigma^b_1(\alpha)$-sentences

$$
\forall n\in\mathrm{Log}\;\forall z\;\exists i\in[1.01^n]\;\mathrm{mistake}_{\mathrm{PHP}}(n,M,z,i),
$$

one for each $\mathsf{PV}(\alpha)$ function symbol $M(i,z)$, stating that the purported length-$1.01^n$ resolution refutation of $\mathrm{PHP}_{(n+1)\to n}$ described by $M(\cdot,z)$ has an invalid step. Then:

1. $\mathrm{Refuter}(s(\mathrm{PHP}_{(n+1)\to n}\vdash_{\mathrm{Res}}\bot)\le 1.01^n)$ is complete for the class of $\mathsf{NP}$ search problems provably total in $T^1_2+\mathrm{dwPHP}(\mathsf{PV})$.
2. A $\forall\Sigma^b_1(\alpha)$-sentence is provable in $T^1_2(\alpha)+\mathrm{dwPHP}(\mathsf{PV}(\alpha))$ if and only if it is provable in $\mathsf{PV}(\alpha)+\mathrm{LB}^{\mathrm{Res}}_{\mathrm{PHP}}(\mathsf{PV}(\alpha))$.

## Expansion

The hardness reduction builds a purported refutation in $n+1$ layers: each layer splits the previous clauses on a fresh variable, and whenever the layer would exceed $M$ clauses, the $2M$ new clauses are routed to $M$ copies through $f$, with weakening chains driven by the $\mathrm{Iter}$ instances $I_y$. Every step is valid except a weakening from $E_{g_y(ans)}$ to the chain node for $y$ at a solution $ans$ of $I_y$, and that step is invalid exactly when $f(g_y(ans))\ne y$; each bottom clause has all $n$ variables, so it is falsified by a single assignment and is a valid weakening of an axiom of $F$ falsified by that assignment. The total size is $O(nLM+|F|)$, below the lower bound, so the refuter must return an $\mathrm{rwPHP}(\mathsf{PLS})$ solution.

The upper bound formalizes the random-restriction proof of Haken's lower bound in the style of Beame and Pitassi: the dual weak pigeonhole principle selects a partial matching under which every clause has small monotone width, and $\Sigma^b_1(\alpha)$-minimization ($\mathsf{PLS}$ reasoning) finds the first clause of large critical-pigeon count, which cannot be validly derived. The witnessing theorem for $T^1_2(\alpha)+\mathrm{dwPHP}(\mathsf{PV}(\alpha))$ converts this proof into the reduction to $\mathrm{rwPHP}(\mathsf{PLS})$.

Similar upper bounds hold for Tseitin formulas on expanders, XOR-lifted formulas, and random $k$-CNFs. For width the analogue is $\mathsf{PLS}$: the width refuter for any unsatisfiable CNF $F$ with $w(F\vdash_{\mathrm{Res}}\bot)>\mathrm{width}(F)$ is $\mathsf{PLS}$-hard, and the refuters for the width lower bounds of the constant-width pigeonhole encoding and of Tseitin formulas are $\mathsf{PLS}$-complete. Since the hardness in item 1 holds for every hard formula, the source reads the result as saying that $\mathrm{rwPHP}(\mathsf{PLS})$ reasoning is necessary for any resolution size lower bound, and that it is consistent with every theory weaker than $T^1_2(\alpha)+\mathrm{dwPHP}(\mathsf{PV}(\alpha))$ that resolution is polynomially bounded; $\mathrm{rwPHP}(\mathsf{PLS})$ is not contained in $\mathsf{PLS}$ in the black-box setting.

## Depends on

- [Refuter problems for resolution lower bounds](resolution-lower-bound-refuter-problems.md)
- [Query total search problems TFNP^dt, decision-tree formulations and the black-box classes](../../../../TheoryOfComputation/complexity-classes/tfnp-hierarchies-and-avoidance/tfnp-proof-complexity-characterizations/query-tfnp-and-formulations.md)

## Proof depends on

- [Haken's lower bound for the pigeonhole principle](../../../propositional-logic/propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md)

## Sources

- Jiawei Li, Yuhao Li, Hanlin Ren, "Finding Bugs in Short Proofs: The Metamathematics of Resolution Lower Bounds", *STOC* 2026, arXiv:2411.15515v2, https://arxiv.org/abs/2411.15515 (Theorem 5.4, Theorem 4.16, Corollary 5.5, Theorem 5.6, Corollary 5.7, Theorem 4.17, Theorems 5.1-5.3, Theorem 3.13, Sections 3.2, 3.3 and 3.5).
