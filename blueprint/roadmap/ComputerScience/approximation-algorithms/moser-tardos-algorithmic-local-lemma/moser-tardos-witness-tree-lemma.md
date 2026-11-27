# Moser-Tardos witness tree lemma

A *witness tree* is a finite rooted tree whose vertices $v$ carry labels $[v] \in \{1, \dots, m\}$ (standing for the events $A_{[v]}$) such that the label of every child is equal or adjacent to the label of its parent; it is *proper* if distinct children of the same vertex carry distinct labels. To each step $t$ of a valid log of the Moser-Tardos algorithm attach the witness tree $\tau(t)$: start from a root labelled by the event resampled at step $t$, scan the earlier steps backwards, and attach each earlier resampled event that is equal or adjacent to the label of some current vertex as a new child of such a vertex of maximum depth (ties broken arbitrarily), skipping the steps whose event is equal or adjacent to no current label. Every $\tau(t)$ is proper (indeed no two of its vertices at the same depth have equal or adjacent labels), and for every fixed witness tree $\tau$,

$$
\Pr[\tau(t) = \tau \text{ for some step } t] \le \prod_{v \in V(\tau)} \Pr[A_{[v]}].
$$

Moreover, if each $A_i$ satisfies $\Pr[A_i] \le x_i \prod_{j \in \Gamma(i)} (1 - x_j)$ with $x_j \in [0,1)$ and $\Gamma(i)$ containing all events adjacent to $A_i$, then the sum of $\prod_{v \in V(\tau)} \Pr[A_{[v]}]$ over all proper witness trees $\tau$ whose root is labelled $i$ is at most $x_i/(1-x_i)$ (Moser and Tardos, Lemma 2.1 and Section 3).

## Proof sketch

Couple the tree with the table: for each vertex $v$, check $A_{[v]}$ on the assignment that gives each variable $u$ of $A_{[v]}$ the table sample indexed by the number of deeper vertices whose events contain $u$. Vertices at the same depth have events sharing no variable, so these checks read distinct table entries and all pass with probability exactly the product; and if $\tau = \tau(t)$, each $A_{[v]}$ held on exactly this assignment when it was resampled, so all checks pass. For the sum, a multitype Galton-Watson process gives each vertex labelled $j$ a child labelled $k$ for each $k \in \Gamma(j) \cup \{j\}$ independently with probability $x_k$; it yields a fixed proper witness tree $\tau$ rooted at $i$ with probability $\frac{1-x_i}{x_i}\prod_{v \in V(\tau)} x_{[v]}\prod_{k \in \Gamma([v])}(1-x_k)$, and these probabilities sum to at most $1$ (for $x_i = 0$ every product is $0$).

## Depends on

- [Moser-Tardos resampling algorithm in the variable model](moser-tardos-algorithm.md)

## Sources

- Robin A. Moser and Gábor Tardos, "A Constructive Proof of the General Lovász Local Lemma", Journal of the ACM 57(2), 2010.
