# Protection systems in the access-matrix model

A *protection system* in the model of Harrison, Ruzzo and Ullman, with generic rights in a type $R$, is a finite set of commands; the paper takes the set of generic rights finite, and nothing below uses it. A *configuration* is a triple $(S, O, P)$ of a set $S$ of subjects, a finite set $O \supseteq S$ of objects, both made of names from a type $N$, and an access matrix $P$ assigning to each pair $(s, o) \in S \times O$ a set $P[s, o] \subseteq R$ of rights. The paper takes each created subject or object to be a new symbol, so its model is the case of an infinite type $N$; with a finite $N$ creation can fail for lack of names. The matrix is recorded as a function on all pairs of names that is empty outside $S \times O$, so each configuration of the paper is recorded in exactly one way.

Each command $\alpha(X_1, \ldots, X_k)$ has formal parameters, a condition that is a conjunction of tests $r \in P[X_i, X_j]$, and a body that is a sequence of primitive operations: enter $r$ into $(X_i, X_j)$, delete $r$ from $(X_i, X_j)$, create or destroy a subject $X_i$, create or destroy an object $X_i$. A primitive operation turns a configuration $(S, O, P)$ into a new one only when its precondition holds:

- enter $r$ into $(s, o)$ and delete $r$ from $(s, o)$ need $s \in S$ and $o \in O$, and add $r$ to, or remove $r$ from, $P[s, o]$;
- create subject $s$ needs $s \notin O$, and adds $s$ to $S$ and to $O$ with an empty row and an empty column; create object $o$ needs $o \notin O$, and adds $o$ to $O$ with an empty column;
- destroy subject $s$ needs $s \in S$, and removes $s$ from $S$ and from $O$; destroy object $o$ needs $o \in O \setminus S$, and removes $o$ from $O$;

and every other cell of the new matrix keeps its rights. Running $\alpha$ with actual parameters $x_1, \ldots, x_k$, which may be any names, on a configuration $Q$ gives $Q$ itself if some test of the condition fails in $Q$. Otherwise it gives the configuration reached by executing the body with each $x_i$ in place of $X_i$, and it gives no configuration if some operation of the body cannot be executed. A configuration is *reachable* from $Q$ if finitely many runs of commands of the system lead to it from $Q$.

A configuration $Q$ *leaks* the right $r$ if some command of the system, run on $Q$ with actual parameters for which its condition holds in $Q$, can execute an initial segment of its body whose last operation enters $r$ into a cell that did not contain $r$ just before; the rest of the body need not be executable. A configuration $Q_0$ is *unsafe* for $r$ if some configuration reachable from $Q_0$ leaks $r$, and *safe* for $r$ otherwise.

## Sources

- M. A. Harrison, W. L. Ruzzo and J. D. Ullman, "Protection in operating systems", *Communications of the ACM* 19(8):461–471, 1976: Section 3 (protection systems, configurations, primitive operations and commands) and Section 4 (leaks, safety)
