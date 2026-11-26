# Karp–Luby–Madras: an FPRAS for counting DNF models

There is a randomized algorithm that, given a DNF formula $\varphi$ with $m$ terms over $n$ variables and $\varepsilon, \delta \in (0,1)$, outputs an estimate $\hat Z$ with $\Pr[|\hat Z - Z| \le \varepsilon Z] \ge 1 - \delta$, where $Z$ is the model count of $\varphi$, in time polynomial in $n$, $m$, $1/\varepsilon$ and $\log(1/\delta)$. Thus $\#\mathrm{DNF}$, although $\#\mathsf{P}$-complete to compute exactly, admits a fully polynomial randomized approximation scheme.

## Proof sketch

Sample a term $T_i$ with probability proportional to its number of models $2^{n - |T_i|}$ (consistent terms), then a uniform model $x$ of $T_i$, and accept if $i$ is the first term satisfied by $x$; the acceptance probability is $Z / \sum_i 2^{n-|T_i|} \ge 1/m$, so $O(m \varepsilon^{-2} \log(1/\delta))$ samples estimate it within relative error $\varepsilon$.

## Depends on

- [Disjunctive normal form](disjunctive-normal-form.md)

## Proof depends on

- [Counting models of DNF formulas is #P-complete](dnf-model-counting-sharp-p-complete.md)

## Sources

- R. M. Karp, M. Luby and N. Madras, "Monte-Carlo Approximation Algorithms for Enumeration Problems", Journal of Algorithms 10(3), 429–448, 1989.
- M. Mitzenmacher and E. Upfal, Probability and Computing, 2nd ed., Cambridge University Press, 2017.
