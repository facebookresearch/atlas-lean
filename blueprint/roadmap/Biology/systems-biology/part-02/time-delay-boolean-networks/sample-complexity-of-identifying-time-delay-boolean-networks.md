# Sample complexity of identifying time-delay Boolean networks

**Setting.** A time-delay Boolean network on $n$ genes $V$ assigns to each target gene $z$ a Boolean function $g$ of at most $K$ input genes together with one relation: similarity $g\sim z$, prerequisite $g\prec z$, or prerequisite $g \prec \bar z$. Data are input/output pairs: an input expression pattern on $V$ and the resulting output pattern, where under a prerequisite with $g = 1$ either output value of $z$ may occur.

**Proposition 1 (uniqueness condition).** Suppose that for every subset of $2K$ genes, all $2^{2K}$ assignments of Boolean values appear among the input patterns, each together with all of its possible output values of the target gene. Then the network consistent with the data, if one exists, is unique.

**Proposition 2 (one sub-assignment is missed rarely).** For uniformly random input patterns, the probability that one fixed sub-assignment of $2K$ genes, together with all of its possible target outputs, fails to appear among $m$ patterns is at most

$$2\Big(1 - \frac{1}{2^{2K+1}}\Big)^{m}.$$

**Theorem 1 (sufficient sample size).** For a time-delay Boolean network on $n$ nodes with maximum indegree $K$,

$$m = O\big(2^{2K+1}(2K + \alpha)\log n\big)$$

uniformly random input patterns suffice for exact identification with probability at least $1 - n^{-\alpha}$.

**Theorem 2 (worst-case lower bound).** If the maximum indegree is at most $K$, at least

$$\Omega\big(2^{K} + K\log n\big)$$

input/output pairs are required for identification in the worst case.

## Expansion

Proposition 1: for similarity this is the classical argument for deterministic Boolean networks. For a prerequisite $g\prec z$ some input value of $g$'s genes yields both outputs $0$ and $1$ of $z$. When all assignments of every $2K$-subset appear with all outputs, any candidate regulator set other than the true one meets an input on which $z$ is visibly non-deterministic, so it cannot reproduce the data.

Proposition 2: write $q = 2^{-2K}$. The sub-assignment appears exactly $t$ times with probability $\binom{m}{t}q^{t}(1-q)^{m-t}$. With $t \ge 1$ appearances, the chance that the two possible outputs do not both occur is at most $(1/2)^{t-1}$, and with $t = 0$ it is $1$. Summing,

$$(1-q)^m + \sum_{t=1}^{m}\binom{m}{t}q^t(1-q)^{m-t}\Big(\tfrac12\Big)^{t-1} = 2\Big(1-\frac q2\Big)^m - (1-q)^m \le 2\Big(1 - \frac{1}{2^{2K+1}}\Big)^m .$$

Theorem 1: a union bound over at most $n^{2K}$ gene subsets and $2^{2K}$ assignments bounds the failure probability of Proposition 1's condition by $2^{2K}n^{2K}\cdot 2(1 - 2^{-(2K+1)})^m$. This is below $p$ once

$$m > \ln 2\cdot 2^{2K+1}\Big(2K + 1 + 2K\log n + \log\frac1p\Big)$$

(logarithms base $2$), and $p = n^{-\alpha}$ gives the stated order.

Theorem 2 is a counting bound. There are $\Omega(n^K)$ choices of inputs per node, $2^{2^K}$ Boolean functions and $3$ relations, hence $\Omega\big((2^{2^K}n^K\cdot3)^n\big)$ networks, while one input pattern has at most $2^n$ distinguishable outputs. Identification therefore needs at least $\log_{2^n}\big((2^{2^K}n^K\cdot 3)^n\big) = 2^K + K\log_2 n + \log_2 3$ pairs. Both bounds have the same form as for classical Boolean networks: the extra prerequisite relations cost only constant factors.

## Depends on

- [Time-delay Boolean networks with prerequisite and similarity relations](time-delay-boolean-networks-with-prerequisite-and-similarity-relations.md)

## Sources

- T.-H. Chueh, H. H.-S. Lu, "Inference of biological pathway from gene expression profiles by time delay boolean networks", PLoS ONE 7(8) (2012) e42095, section Theoretical Results: Proposition 1, Proposition 2, Theorem 1 and Theorem 2 with their proofs, <https://doi.org/10.1371/journal.pone.0042095>, PMCID PMC3432056.
- T. Akutsu, S. Miyano, S. Kuhara, "Identification of genetic networks from a small number of gene expression patterns under the Boolean network model", Pacific Symposium on Biocomputing 4 (1999) 17–28, <https://doi.org/10.1142/9789814447300_0003>.
