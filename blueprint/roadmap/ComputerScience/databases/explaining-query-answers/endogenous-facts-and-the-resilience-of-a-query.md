# Endogenous facts and the resilience of a query

In the study of explanations, a database $D$ is split into exogenous facts $D_x$, which are taken as given, and endogenous
facts $D_n$, which may be changed: $D = D_x \cup D_n$. For resilience the split is fixed by the query: each relation name of
$q$ is marked endogenous or exogenous, and $D_n$ consists of the facts of the endogenous relations. (The Shapley value of a
fact allows an arbitrary split of the facts.) For a Boolean query $q$, the pair $(D, k)$ belongs to $\mathrm{RES}(q)$
when $D \models q$ and some set $\Gamma \subseteq D_n$ with $|\Gamma| \le k$ satisfies $D \setminus \Gamma \not\models q$; such a
$\Gamma$ is a contingency set (the source's term from its notion of responsibility). When some contingency set exists, the *resilience* of $q$ on $D$ is the least such $k$, the minimum
number of endogenous facts whose deletion makes $q$ false; otherwise it is undefined (taken as $\infty$). This happens when
$D \not\models q$, and also when $D \models q$ but the endogenous facts cannot falsify it: for $q = \exists x\, R(x)$ with $R$ exogenous
and nonempty. For queries computable in polynomial time, $\mathrm{RES}(q)$ is in NP.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [The complexity class NP](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md)

## Sources

- C. Freire, W. Gatterbauer, N. Immerman and A. Meliou, "The complexity of resilience and responsibility for self-join-free conjunctive queries", *Proc. VLDB Endowment* 9(3) (2015) 180–191; extended version arXiv:1507.00674 <https://arxiv.org/abs/1507.00674>, Section 2 (endogenous and exogenous tuples, Definition 2 in the PVLDB edition (Definition 2.1 in the extended version)).
