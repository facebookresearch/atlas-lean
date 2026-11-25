# Semi-naive evaluation is correct

For a Datalog program $P$ and a finite EDB instance $I$, let naive evaluation compute
$J_0 = \emptyset$ and $J_{i+1} = T_{P,I}(J_i)$ synchronously. Semi-naive evaluation computes $J'_1 = T_{P,I}(\emptyset)$
(all rules fired once, so rules with EDB-only bodies contribute), sets $\Delta_1 = J'_1$, and for $i \ge 1$ fires
only the rule instances whose EDB body atoms hold in $I$, whose IDB body atoms all hold in $J'_i$, and at least one
of whose IDB body atoms is a fact of $\Delta_i$, giving $J'_{i+1} = J'_i \cup$ (new facts) and
$\Delta_{i+1} = J'_{i+1} \setminus J'_i$. Then $J'_i = J_i$ for every $i \ge 1$, so semi-naive evaluation produces
the same sequence of cumulative IDB instances as naive evaluation; after finitely many rounds $\Delta_i = \emptyset$,
and then $J'_i$ is the least fixed point of $T_{P,I}$, the IDB part of $P(I)$. The statement is for this
synchronous schedule.

## Depends on

- [Datalog programs and the immediate consequence operator](datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [Least model equals least fixpoint for Datalog](least-model-equals-least-fixpoint-for-datalog.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995 (authors' web edition), Section 13.1, Algorithm 13.1.1 (Basic Seminaive Algorithm), p. 315, whose correctness is Exercise 13.3. <http://webdam.inria.fr/Alice/pdfs/all.pdf>
