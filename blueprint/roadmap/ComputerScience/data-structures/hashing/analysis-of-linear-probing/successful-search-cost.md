# Expected cost of a successful linear-probing search

For natural numbers $N$ and $n$, this is $T(N, n) = \frac{1}{n} \sum_{i=0}^{n-1} c(N, i)$, the
average of the [expected insertion costs](insertion-cost.md) $c(N, i)$ for $i = 0, \dots, n - 1$;
for $n = 0$ it is $0$, by the convention that division by zero gives $0$. For $1 \le n \le N$ each
$c(N, i)$ is Knuth's $M(N, i + 1)$, so $T(N, n)$ is the average over the stored items of the
expected cost of their insertion. Knuth's 1963 note (Section 7) observes that a search for an item
makes as many comparisons as its insertion did, so for $1 \le n \le N$ this is the expected number
of probes of a successful search for a uniformly chosen stored item; the definition takes that
observation as the model of a successful search. For $n > N \ge 1$ the average includes the
full-table values $N + 1$ of the insertion cost; for $N = 0$ every insertion cost is $0$, and so is
the average.

## Sources

- D. E. Knuth, "Notes on 'open' addressing", 22 July 1963, typeset by H. Prodinger in 1997,
  Section 7: https://jeffe.cs.illinois.edu/teaching/datastructures/2011/notes/knuth-OALP.pdf
