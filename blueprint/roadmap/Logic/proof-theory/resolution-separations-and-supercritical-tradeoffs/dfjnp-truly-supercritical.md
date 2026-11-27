# de Rezende–Fleming–Janett–Nordström–Pang: truly supercritical trade-offs for resolution and cutting planes

There are two regimes of unsatisfiable $3$-CNF formulas $F_N$ over $N$ variables, of size $S(F_N)$, in which every small refutation must be deep:

1. **Polynomial size.** Resolution refutes $F_N$ in size $s$ polynomial in $N$, but every cutting planes refutation of $F_N$ of size at most $s^{1.4}$ has depth at least $S(F_N)^{2.4}$.
2. **Quasi-polynomial size.** Resolution refutes $F_N$ in size $s$ quasi-polynomial in $N$, but every cutting planes refutation of $F_N$ of size at most $s \cdot \exp\big((\log N)^{1.9}\big)$ has depth superpolynomial in $N$.

Both lower bounds hold for semantic cutting planes, and since cutting planes is at least as strong as resolution they give truly supercritical size-depth trade-offs for resolution too. The precise version takes suitable integers $3 \le c < k$ (with $k < n/(2\log n)$, where $n$ is the base number of variables), a real $\delta \in (0, 0.9)$ and a lifting parameter $m \ge (50n/\delta)^{2/\delta}$: the formulas have resolution refutations of size $m^{O(k)} (4n)^{k}$, while every semantic cutting planes refutation of size at most $\tfrac{1}{2} m^{(1-\delta)(k+c)}$ has depth $\Omega(n^{k}/k)$; a sufficiently large constant $k$ with $c = \lfloor 0.41k \rfloor$, $\delta = 1/200$ and $m = n^{500}$ gives the first regime, and $k = \lfloor n/(4\log n) \rfloor$ with $c = \lfloor\sqrt{k}\rfloor$, $\delta = 1/(4\sqrt{k})$ and $m = \lfloor n^{12\sqrt{k}} \rfloor$ the second.

## Proof sketch

The base result is a supercritical width-depth trade-off for resolution: Tseitin formulas over compressed cylinder graphs have resolution refutations of width $k + 3$, but every refutation of width at most $k + c$ has depth $\Omega(n^{k}/(k + c))$, proved by refining the compression scheme for the cops-and-robber game. The formula is then composed with the indexing gadget on $m$ data bits and rewritten as a $3$-CNF. A cutting planes refutation of size $s$ and depth $d$ yields a triangle-DAG of size $s$ and depth $d$ for the falsified-clause search problem of the composed formula, and a tight width-depth lifting theorem for triangle-DAGs converts a triangle-DAG of size $\tfrac{1}{2} m^{(1-\delta)w}$ and depth $d$ into a resolution refutation of the base formula of width $w$ and depth $dw$. With $w = k + c$ the base trade-off forces large $d$. The resolution upper bound lifts the width-$(k+3)$ refutation through the gadget.

## Depends on

- [Supercritical trade-offs in proof complexity](supercritical-tradeoff.md)

## Sources

- S. F. de Rezende, N. Fleming, D. Janett, J. Nordström, S. Pang, "Truly supercritical trade-offs for resolution, cutting planes, monotone circuits, and Weisfeiler-Leman", STOC (2025), arXiv:2411.14267 (Theorems 1.2, 2.5, 2.13 and 2.15).
