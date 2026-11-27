# Accumulating CNF builder

Let $\iota$ number the atoms by natural numbers, read a literal
$(n, p)$ as variable $n$ with polarity $p$, and write $1$ and $0$ for the polarities true and
false. For a polarity $p$, a proposition $\varphi$ and a CNF $S$, the CNF
$\mathcal{A}_p(\varphi, S)$ is defined by recursion on $\varphi$, together with the disjoining
builder $\mathcal{O}_p$. For an atom $a$, $\mathcal{A}_p(a, S)$ is the unit clause
$[(\iota(a), p)]$ followed by the clauses of $S$. Conjunction-like nodes thread the accumulator:
$\mathcal{A}_1(A \land B, S) = \mathcal{A}_1(A, \mathcal{A}_1(B, S))$,
$\mathcal{A}_0(A \lor B, S) = \mathcal{A}_0(A, \mathcal{A}_0(B, S))$ and
$\mathcal{A}_0(A \to B, S) = \mathcal{A}_1(A, \mathcal{A}_0(B, S))$. Disjunction-like nodes go
through $\mathcal{O}$: writing $X \mathbin{+\!\!+} S$ for the clauses of $X$ followed by those of
$S$ and $[\,]$ for the empty CNF,
$\mathcal{A}_1(A \lor B, S) = \mathcal{O}_1(A, \mathcal{A}_1(B, [\,])) \mathbin{+\!\!+} S$,
$\mathcal{A}_1(A \to B, S) = \mathcal{O}_0(A, \mathcal{A}_1(B, [\,])) \mathbin{+\!\!+} S$ and
$\mathcal{A}_0(A \land B, S) = \mathcal{O}_0(A, \mathcal{A}_0(B, [\,])) \mathbin{+\!\!+} S$.

An assignment $\sigma$ satisfies $\mathcal{A}_p(\varphi, S)$ exactly when $\varphi$ has truth
value $p$ under $\sigma \circ \iota$ and $\sigma$ satisfies $S$.
