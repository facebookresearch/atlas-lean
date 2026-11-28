# CNF decompositions of propagators and consistency checkers

A CNF decomposition of a propagator is a clause set over the direct encoding of the domains, plus polynomially many auxiliary Boolean variables, on which unit propagation removes exactly the values the propagator removes; a CNF decomposition of a consistency checker makes unit propagation falsify an output variable exactly when the checker detects failure.

**Domains as literal sets.** Fix $n\ge1$ variables $X_1,\dots,X_n$ with nonempty initial finite domains, of sizes $r_1,\dots,r_n$. A domain $\mathbf D$ is identified with the set of literals $X_i=j$ it allows. A **propagator** for a constraint $C$ is a polynomial-time function $f$ from such sets to such sets that is monotone ($\mathbf D'\subseteq\mathbf D\Rightarrow f(\mathbf D')\subseteq f(\mathbf D)$), contracting ($f(\mathbf D)\subseteq\mathbf D$) and idempotent ($f(f(\mathbf D))=f(\mathbf D)$), removes only literals that belong to no solution of $C$ inside $\mathbf D$, and returns $\emptyset$ when it detects that $C$ has no solution in $\mathbf D$. It **detects disentailment** when it returns $\emptyset$ whenever $C$ has no solution in $\mathbf D$, and it **enforces domain consistency** when every literal it keeps belongs to a solution of $C$ inside $\mathbf D$, so that $f(\mathbf D)$ is the [GAC closure](generalized-arc-consistency.md) of $\mathbf D$. A **consistency checker** for $C$ is a polynomial-time monotone function $f$ from literal sets to $\{0,1\}$ such that $f(\mathbf D)=0$ implies that $C$ has no solution in $\mathbf D$; read on the characteristic vector $b_{i,j}=[X_i=j\in\mathbf D]$ it is a monotone Boolean function.

**Induced checker.** A propagator $f_P$ induces the consistency checker $f_C(\mathbf D)=0$ iff $f_P(\mathbf D)=\emptyset$. If $f_P$ enforces domain consistency, this checker is *exact*: $f_C(\mathbf D)=1$ iff $C$ has a solution in $\mathbf D$. Conversely, an exact checker $f_C$ determines the domain consistency propagator $f_P(\mathbf D)=\mathbf D\setminus\{X_i=j: f_C(\mathbf D|_{X_i=j})=0\}$, where $\mathbf D|_{X_i=j}$ removes the other values of $X_i$. The source prints this second map for arbitrary checkers; for a checker that is sound but not exact, one pass of it need not be idempotent, so it is used here only for exact checkers.

**Direct encoding and unit propagation.** The direct encoding has a Boolean variable $x_{i,j}$ for each initial literal $X_i=j$, with the *at-most-one* clauses $\neg x_{i,j}\vee\neg x_{i,k}$ ($j\ne k$) and the *at-least-one* clause $\bigvee_j x_{i,j}$ for each $i$. A current domain is represented by setting $x_{i,j}$ false for every removed literal and leaving the others unset (setting the last remaining value true represents the same domain). Unit propagation on a CNF formula repeatedly sets to true the last unset literal of a clause whose other literals are all false, until a fixpoint or until all literals of some clause are false, which is *producing the empty clause* and ends propagation.

**Definition.** Let $\mathbf x=\{x_{i,j}\}$ and let $\mathbf y$ be a set of auxiliary Boolean variables of size polynomial in $|\mathbf x|$.

1. A CNF decomposition of a propagator $f_P$ is a CNF formula $C_P$ over $\mathbf x\cup\mathbf y$, taken in conjunction with the direct-encoding clauses (which are counted in its size), such that for every domain $\mathbf D$ represented on $\mathbf x$: if $f_P(\mathbf D)=\emptyset$, unit propagation produces the empty clause; otherwise it produces no empty clause and sets $x_{i,j}$ false exactly for the literals $X_i=j\notin f_P(\mathbf D)$.
2. A CNF decomposition of a consistency checker $f_C$ is a CNF formula $C_C$ over $\mathbf x\cup\mathbf y\cup\{z\}$, without the direct-encoding clauses, such that, starting from the representation of $\mathbf D$ with $\mathbf y$ and the output variable $z$ unset, unit propagation never forces a variable of $\mathbf x$, never produces the empty clause, and sets $z$ to false iff $f_C(\mathbf D)=0$. The value of $z$ is read off after propagation, never fixed from outside.

The size of a decomposition is its number of literal occurrences. For a propagator decomposition this includes the direct-encoding clauses: the at-most-one clauses have $\sum_i r_i(r_i-1)$ literal occurrences and the at-least-one clauses $\sum_i r_i$, so $\sum_i r_i^2$ in total.

## Depends on

- [Generalized arc consistency](generalized-arc-consistency.md): domain consistency, the GAC closure computed by a domain consistency propagator.

## Proof depends on

None.

## Expansion

Example from the source. For the table constraint on $X_1,X_2\in\{a,b\}$ with allowed tuples $\langle a,a\rangle,\langle b,b\rangle,\langle a,b\rangle$, introduce one auxiliary $y_k$ per tuple; together with the direct-encoding clauses of $X_1$ and $X_2$, the clauses $x_{1a}\to y_1\vee y_3$, $x_{2a}\to y_1$, $x_{1b}\to y_2$, $x_{2b}\to y_2\vee y_3$, $y_k\to$ (each literal of tuple $k$), and $y_1\vee y_2\vee y_3$ (added to detect failure) form a CNF decomposition of the domain consistency propagator: removing $a$ from $X_1$ forces $y_1$ false and then $x_{2a}$ false. Omitting the direct-encoding clauses and the clauses that prune input literals, and replacing the last clause by $\neg y_1\wedge\neg y_2\wedge\neg y_3\to\neg z$ gives a CNF decomposition of the consistency checker: removing $a$ from $X_1$ and $b$ from $X_2$ forces all $y_k$ and then $z$ false.

The two maps are the source's equations (1)–(2), attributed there to Bessiere, Hebrard, Hnich and Walsh. For an exact checker the second map keeps exactly the literals with a support, so it is the domain consistency propagator and is idempotent. For a merely sound checker it can fail to be idempotent: for the constraint on Boolean $X,Y$ allowing only $X=0,Y=1$, the checker $b_{X,0}\wedge(b_{X,1}\vee b_{Y,1})$ is monotone and sound; from full domains one pass removes $X=1$, and a second pass then also removes $Y=0$.

The propagator definition follows Schulte and Stuckey, whose propagators are monotonically decreasing functions on domains and may be idempotent. The source notes that a checker decomposition used in practice may rely on direct-encoding clauses; then negative input literals are replaced by disjunctions of positive ones of the same variable.

## Sources

- C. Bessiere, G. Katsirelos, N. Narodytska and T. Walsh, "Circuit complexity and decompositions of global constraints", *Proceedings of the Twenty-First International Joint Conference on Artificial Intelligence (IJCAI 2009)*, 412–417, [https://www.ijcai.org/proceedings/2009/76](https://www.ijcai.org/proceedings/2009/76). Definitions 1, 2, 4 and 5, Examples 1–2, the maps between propagators and checkers (equations (1)–(2)), the direct encoding and unit propagation in §§2–3, and the remark after the input-polarity lemma in §4, of arXiv:0905.3757v1, [https://arxiv.org/abs/0905.3757v1](https://arxiv.org/abs/0905.3757v1).
- C. Schulte and P. J. Stuckey, "Efficient constraint propagation engines", *ACM Transactions on Programming Languages and Systems* 31(1) (2008), article 2, doi:10.1145/1452044.1452046. Propagators and their correctness in §2, idempotence in §4 of arXiv:cs/0611009v1, [https://arxiv.org/abs/cs/0611009v1](https://arxiv.org/abs/cs/0611009v1).
