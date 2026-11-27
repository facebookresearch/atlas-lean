# Establishment of a mutation on a multicopy plasmid under random segregation

Each cell carries exactly $n$ copies of a non-transmissible plasmid, $i$ of them mutant. A cell of type $i$ divides at rate $\lambda_i$ and dies at rate $\mu_i$. Before division every plasmid is replicated once (neglect new mutation, so a type-$i$ cell holds $2i$ mutant and $2n - 2i$ wild-type copies), and the $2n$ copies are split uniformly at random into two daughters of $n$ copies each. Hence a daughter receives $k$ mutant copies with the hypergeometric probability

$$h_{i}(k) = \frac{\binom{2i}{k}\binom{2n - 2i}{n - k}}{\binom{2n}{n}},$$

and the daughter pair is $\{k, 2i - k\}$ with probability $2h_i(k)$ for $k \ne i$ and $h_i(i)$ for $k = i$. Assume the wild type is subcritical, $\lambda_0 < \mu_0$, so type-$0$ lineages die out.

**Proposition.** While mutants are rare their lineages form a multitype branching process on types $1, \dots, n$; the establishment probability $p_{\mathrm{est}}(n)$ of a single mutant copy is $1 - q_1$, where $(q_1, \dots, q_n)$ is the minimal solution in $[0,1]^n$ of

$$(\lambda_i + \mu_i)\,q_i = \mu_i + \lambda_i \sum_{\{k, k'\}} P_i(\{k,k'\})\, q_k q_{k'}, \qquad q_0 = 1.$$

For $n = 1$, $p_{\mathrm{est}}(1) = 1 - \mu_1/\lambda_1$ when $\lambda_1 > \mu_1$. For $n = 2$, with $r = \mu_1/\lambda_1$ for heterozygous cells and $r_2 = \mu_2/\lambda_2 < 1$ for mutant homozygotes,

$$p_{\mathrm{est}}(2) = \frac14 - \frac34 r + \frac14\sqrt{9 - 6r + 9r^2 - 8r_2}.$$

## Depends on

This node has no prerequisites.

## Proof depends on

- [Limiting extinction probability in the supercritical case](../../../../Probability/branching-processes/linear-birth-death-process/tendsto-extinction-prob-of-lt.md)
- [Certain extinction in the critical and subcritical cases](../../../../Probability/branching-processes/linear-birth-death-process/tendsto-extinction-prob-of-le.md)

## Expansion

The extinction probabilities satisfy the first-step equations of the branching process: a type-$i$ cell first dies (probability $\mu_i/(\lambda_i + \mu_i)$) or divides into an unordered daughter pair. For $n = 2$ a heterozygote ($i = 1$) produces two heterozygotes with probability $\binom21\binom21/\binom42 = 2/3$ and one mutant homozygote plus one doomed wild type with probability $1/3$, while a mutant homozygote is a single-type birth–death process with $q_2 = r_2$. The equation $(1 + r)q_1 = r + \tfrac23 q_1^2 + \tfrac13 r_2$ is the quadratic $2q_1^2 - 3(1+r)q_1 + 3r + r_2 = 0$, whose smaller root gives the displayed $1 - q_1$. Random segregation creates "segregational drift": each division of a heterozygote can lower the number of mutant copies in one daughter, so without dosage effects establishment becomes less likely as $n$ grows, even though mutational supply grows with $n$. The establishment probability computed here is the factor $p_{\mathrm{est}}$ in the [rescue probability](probability-of-evolutionary-rescue-from-de-novo-mutations.md).

## Sources

- M. Santer and H. Uecker, "Evolutionary Rescue and Drug Resistance on Multicopy Plasmids", Genetics 215 (2020), 847–868, Equation 1, Equations 4–5 and Appendix A, <https://doi.org/10.1534/genetics.119.303012> (PMC7337077).
