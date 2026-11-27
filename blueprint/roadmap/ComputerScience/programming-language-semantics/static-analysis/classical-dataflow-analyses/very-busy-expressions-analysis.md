# Very busy expressions analysis

Let a program be given as a control-flow graph whose nodes are statements, with an exit node. A nontrivial expression is *very busy* at a program point if, on every path from that point to the exit, it is evaluated before any of its variables is assigned.

*Very busy expressions analysis* approximates, for every node $v$, the set of expressions that are very busy at the point before $v$. It uses the lattice $(\mathcal{P}(\mathrm{Exps}), \supseteq)$ and the functions $\mathrm{exps}$ and $\downarrow X$ of [available expressions analysis](available-expressions-analysis.md), with

$$\mathrm{JOIN}(v) = \bigcap_{w \in \mathrm{succ}(v)} [\![w]\!].$$

The constraints are

- $[\![\mathit{exit}]\!] = \emptyset$;
- $[\![v]\!] = (\mathrm{JOIN}(v) \downarrow X) \cup \mathrm{exps}(E)$ for an assignment $X = E$;
- $[\![v]\!] = \mathrm{JOIN}(v) \cup \mathrm{exps}(E)$ for a branch condition $E$ and for an output statement $E$;
- $[\![v]\!] = \mathrm{JOIN}(v)$ for every other node.

The right-hand sides are monotone, so the constraints have a least solution in this lattice, the largest family of sets satisfying them. It is a backward *must* analysis. The property concerns paths that reach the exit, so it does not license moving an evaluation earlier by itself: in $\mathtt{while}\ b\ \{\ \mathtt{skip}\ \};\ \mathtt{output}\ 1/x$, the expression $1/x$ is very busy before the loop, yet an execution in which $b$ stays true never evaluates it, and evaluating it before the loop turns that divergence into a division error when $x = 0$. Evaluating a very busy expression at an earlier point is harmless when its evaluation is total and has no side effects. Replacing its later evaluations by that early value needs more: no variable of the expression may be assigned on any path, terminating or not, from the early point to a replaced evaluation. Paths that never reach the exit are not covered by the analysis. Starting from $x = 0$, let one branch output $x + 1$ and exit, and the other assign $x \leftarrow 1$, output $x + 1$ and enter a self-loop. Then $x + 1$ is very busy before the branch, but replacing both outputs by its value there changes the second output from $2$ to $1$. Each transfer function has the gen/kill form: for an assignment $X = E$, $\mathit{gen}[v] = \mathrm{exps}(E)$ and $\mathit{kill}[v]$ is the set of expressions containing $X$.

## Depends on

- [Available expressions analysis](available-expressions-analysis.md)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>: Section 5.6 (very busy expressions: $\mathrm{JOIN}$ by intersection over successors, the constraint for assignments, the exit constraint, and code hoisting) and Section 5.8 (backward and must analyses).
