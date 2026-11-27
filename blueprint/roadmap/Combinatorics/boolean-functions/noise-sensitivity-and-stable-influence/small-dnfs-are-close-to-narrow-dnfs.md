# Small DNFs and CNFs are close to narrow ones

For every DNF $\varphi$ with $s$ terms and every $\varepsilon > 0$, there is a DNF $\varphi'$ with at most $s$ terms, each of width (number of distinct variables) at most $\log_2(s/\varepsilon)$, such that $\Pr_x[\varphi(x) \ne \varphi'(x)] \le \varepsilon$. The same holds for CNFs with clauses in place of terms.

## Proof sketch

Delete every term of width greater than $\log_2(s/\varepsilon)$: each such term is satisfied with probability less than $\varepsilon/s$, and the deleted terms change the function only on inputs satisfying one of them, a set of measure less than $s \cdot \varepsilon/s$.

## Depends on

- [Disjunctive normal form](../../../Logic/propositional-logic/boolean-clones-and-cnf-encodings/cnf-gadgets-and-encodings/disjunctive-normal-form.md)
- [Relative Hamming distance on the Boolean cube](../../../TheoryOfComputation/pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/bool-dist.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
