# Haldane HMM and the digital twin randomization test

Consider $n$ offspring with phased haplotypes $X^m, X^f \in \{0,1\}^{n \times p}$ at $p$ biallelic sites, parental haplotypes $A = (M^a, M^b, F^a, F^b)$, genotypes $\bar X = X^m + X^f$, and phenotype $Y$. For a partition $\mathcal G$ of the sites and $g \in \mathcal G$, the **local null hypothesis** is

$$H_0^g : \; Y \perp\!\!\!\perp X_g \mid (X_{-g}, A).$$

**Haldane HMM.** For one offspring and chromosome, the maternal-origin path $U^m \in \{a, b\}^p$ is a Markov chain with $\mathbb P(U_1^m = a) = \tfrac12$ and

$$\mathbb P(U_j^m = U_{j-1}^m \mid U^m_{1:(j-1)}) = \tfrac12\big(1 + e^{-2 d_j}\big),$$

where $d_j$ is the genetic distance (Morgans) between sites $j-1$ and $j$; given $U^m$, independently $X_j^m = M_j^{U_j^m}$ with probability $1 - \epsilon$ ($\epsilon$ the de novo mutation rate). The paternal haplotype follows the same model with $F$, independently given $A$.

**Digital twin test.** Fix a statistic $T$. Compute $t^* = T((X_{-g}, X_g), Y)$; for $k = 1, \dots, K$ draw a digital twin $\tilde X_g$ from the law of $X_g \mid (X_{-g}, A)$, independently of $(X_g, Y)$, and compute $t_k = T((X_{-g}, \tilde X_g), Y)$; report

$$v = \frac{1 + \#\{k : t^* \le t_k\}}{K + 1}.$$

**Proposition.** If $X \mid A$ follows the Haldane HMM, then under $H_0^g$ the law of $v$ stochastically dominates $\mathrm{Uniform}(0, 1)$: $v$ is a valid finite-sample $p$-value, for any choice of $T$.

**Special case.** The transmission disequilibrium test is the digital twin test with $g$ the whole chromosome containing site $j$ and $T(X) = \sum_{i=1}^n \bar X_j^{(i)}\,\mathbf 1\{Y_i = 1\}$, evaluated exactly rather than asymptotically.

## Depends on

- [Haldane's map function](../../../../population-genetics/linkage-disequilibrium-and-haldane-s-map-functio/haldane.md)
- [Valid p-value](../../../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

Under $H_0^g$, $(X_g, Y)$ and $(\tilde X_g, Y)$ have the same joint law given $(X_{-g}, A)$, so $t^*, t_1, \dots, t_K$ are exchangeable and the rank of $t^*$ is (super-)uniform; this is the conditional randomization test. Validity needs only the known meiosis model, not a correct phenotype model, so $T$ may be the negative prediction loss of a penalized regression trained on an external GWAS, which raises power without affecting validity. The switch probability $\tfrac12(1 + e^{-2d})$ is one minus Haldane's recombination fraction. Twins conditioned also on the ancestral states at group boundaries make the Markov structure split across groups, giving jointly independent null $p$-values (Theorem 1) suitable for SeqStep or accumulation tests with FDR control.

## Sources

- S. Bates, M. Sesia, C. Sabatti, E. Candès, "Causal inference in genetic trio studies", Proceedings of the National Academy of Sciences 117(39) (2020) 24117–24126, Eqs. 1–4, Algorithm 1, Proposition 1, Theorem 1, and Methods ("The Haldane HMM"), <https://doi.org/10.1073/pnas.2007743117>, PMCID PMC7533659.
