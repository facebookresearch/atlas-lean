# Kim's triangle-free graphs with small independence number

Every sufficiently large $n$ has a triangle-free graph $G$ on $n$ vertices with

$$\alpha(G) \le 9 \sqrt{n \log n}$$

(natural logarithm). Kim builds $G$ by a semi-random ("nibble") block construction: in each round every edge that does not close a triangle with the edges chosen so far is added independently with probability $\theta / \sqrt n$, $\theta = (\log n)^{-2}$, and a maximal disjoint family of conflicting pairs and triples is removed. Martingale concentration keeps the parameters of the process near their expected trajectories, which follow Spencer's differential equation.

## Background

- [Azuma's inequality](../../../Probability/concentration-inequalities/azuma-inequality.md): the bounded-increment martingale inequality; Kim's analysis uses Azuma–Hoeffding-type martingale inequalities adapted to parameters that occasionally change a lot (Section 4 of the paper).
- [Kim–Vu polynomial concentration](../../../Probability/concentration-inequalities/kim-vu-polynomial-concentration/README.md): a later, general concentration inequality for exactly this situation, by Kim and Vu.

## Sources

- J. H. Kim, "The Ramsey number R(3,t) has order of magnitude t²/log t", *Random Structures & Algorithms* 7 (1995), 173–207, Theorem 1.1, and Section 1.1 (block construction).
