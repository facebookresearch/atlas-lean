# Kim's lower bound for R(3, t)

For every $\varepsilon > 0$ and all sufficiently large $t$,

$$R(3, t) \ge (1 - \varepsilon) \frac{t^2}{162 \log t},$$

that is, $R(3,t) \ge c(1 - o(1))\, t^2/\log t$ with $c = 1/162 = 1/(2 \cdot 9^2)$. It follows from [Kim's triangle-free graphs](exists-clique-free-three-indep-num-le.md): a triangle-free graph on $n$ vertices with $\alpha < t$ shows $R(3, t) > n$. Earlier lower bounds were of order $t^2 / (\log t)^2$ (Erdős 1961, with later simplifications and better constants by Spencer, Bollobás, Erdős–Suen–Winkler and Krivelevich), and Spencer had shown that $R(3,t)/(t/\log t)^2 \to \infty$. Bohman recovered the order $t^2/\log t$ from the triangle-free process.

## Informally uses

- [Kim's triangle-free graphs with small independence number](exists-clique-free-three-indep-num-le.md): the construction.

## Background

- [Second moment method for counts of events](../../../Combinatorics/probabilistic-combinatorics/first-and-second-moment-methods/measure-real-forall-not-mem-le.md) and [Lovász local lemma, general form](../../../Combinatorics/probabilistic-combinatorics/lovasz-local-lemma-general-finite.md): the basic probabilistic existence tools that the semi-random method refines.

## Sources

- J. H. Kim, "The Ramsey number R(3,t) has order of magnitude t²/log t", *Random Structures & Algorithms* 7 (1995), 173–207, the consequence of Theorem 1.1 stated after Corollary 1.2.
- T. Bohman, "The triangle-free process", arXiv:0806.4375 (2008), Theorem 2.
