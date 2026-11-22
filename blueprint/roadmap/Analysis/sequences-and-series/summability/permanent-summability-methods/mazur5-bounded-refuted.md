# Negative answer to Scottish Book Problem 5 for bounded sequences

There is no real matrix
$(a_{ik})_{i,k \in \mathbb{N}}$ that is a permanent matrix method such that for every bounded real
sequence $x$ and every real number $S$, the matrix sums $x$ to $S$ if and only if $x$ is
asymptotically convergent to $S$.

Proof: Mazur's addendum Ad 5 (2) to the problem states: if a method $(a_{ik})$ sums all convergent
sequences and every bounded sequence summable by the method is asymptotically convergent, then
there is an increasing sequence of integers $(k_n)$ of density $1$ such that for every bounded
sequence $(\xi_n)$ summable by the method, the sequence $(\xi_{k_n})$ converges. Suppose a
permanent method $a$ summed exactly the bounded asymptotically convergent sequences (to the right
limits). Then $a$ satisfies both hypotheses of (2), which yields such a sequence $(k_n)$. Let
$J = \mathbb{N} \setminus \{k_{m^2} : m \in \mathbb{N}\}$; since $k_{m^2} \ge m^2$, the excluded set
has density $0$, so $J$ has density $1$. Let $\xi_n = 0$ for $n \in J$ and $\xi_n = 1$ otherwise.
Then $\xi$ is bounded and asymptotically convergent to $0$, so $a$ sums $\xi$; but $\xi_{k_n} = 1$
exactly when $n$ is a perfect square, so $(\xi_{k_n})$ diverges, contradicting (2). (The Cesàro
method does not satisfy the hypothesis of (2): $(-1)^n$ is Cesàro summable but not asymptotically
convergent.)

## Sources

- S. Mazur, Problem 5 of the Scottish Book, addendum Ad 5, PDF p.5 / printed p.2 of the typescript. Ad 5 (2) states verbatim: "If a method (a_{ik}) sums all the convergent sequences and every bounded sequence summable by the sequence [sic — the method] is asymptotically convergent, then there exists a sequence of increasing integers {kₙ} with density 1, such that for every bounded sequence {ξₙ} summable by this method, the sequence {ξ_{kₙ}} is convergent." The typescript then draws the corollary verbatim: "from (2) it follows that a permanent method summing all bounded asymptotically convergent sequences must also sum some other bounded sequences", i.e. no permanent method sums exactly the bounded asymptotically convergent sequences. Ad 5 (1) alone does not settle the bounded question.
