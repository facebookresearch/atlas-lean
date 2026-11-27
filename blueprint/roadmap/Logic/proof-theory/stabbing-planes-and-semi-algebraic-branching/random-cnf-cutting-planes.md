# Random logarithmic-width CNFs are hard for cutting planes

For every constant $c > 1$, let $C$ be a random $k$-CNF formula with $n$ variables and $m = O(n 2^{k})$ clauses, where $k \ge c \log n$. Then, with high probability, every cutting planes (or semantic cutting planes) refutation of $C$ has size $2^{n^{\Omega(1)}}$ (Hrubeš–Pudlák). For $m \ge C_0 n 2^{k}$ with a sufficiently large constant $C_0$ the formula is unsatisfiable with high probability; for smaller $m$ the statement holds trivially when $C$ is satisfiable. Fleming, Pankratov, Pitassi and Robere independently obtained a similar lower bound for random $\Theta(\log n)$-CNFs. These were the first cutting planes lower bounds for random formulas. The case of constant $k$ is not covered: the method needs monotone circuit lower bounds for certificates that are not available in that regime.

## Proof sketch

Split the variables into two halves $X_0, X_1$ and write each clause as $C_i = C_i^0 \cup C_i^1$ with $C_i^b$ over $X_b$. An **$X_0, X_1$-unsatisfiability certificate** for $C = \{C_1, \dots, C_m\}$ is a monotone Boolean function $F$ on subsets $A \subseteq [m]$ with $F(A) = 1$ whenever $\{C_i^1 : i \notin A\}$ is satisfiable and $F(A) = 0$ whenever $\{C_i^0 : i \in A\}$ is satisfiable; one exists exactly when $C$ is unsatisfiable. By Pudlák's interpolation for cutting planes, a cutting planes refutation of size $s$ yields a certificate computed by a monotone real circuit of size $\operatorname{poly}(s)$. Hrubeš and Pudlák show that, with high probability over the random $k$-CNF with $k \ge c \log n$, every certificate requires monotone real circuits of size $2^{n^{\Omega(1)}}$, which gives the bound.

## Proof depends on

- [Haken–Cook / Pudlák: exponential lower bounds for monotone real circuits](haken-cook-monotone-real.md)

## Sources

- P. Hrubeš, P. Pudlák, "Random formulas, monotone circuits, and interpolation", FOCS (2017) (Theorems 1 and 2).
- N. Fleming, D. Pankratov, T. Pitassi, R. Robere, "Random Theta(log n)-CNFs are hard for cutting planes", FOCS (2017); Journal of the ACM 69 (2022).
