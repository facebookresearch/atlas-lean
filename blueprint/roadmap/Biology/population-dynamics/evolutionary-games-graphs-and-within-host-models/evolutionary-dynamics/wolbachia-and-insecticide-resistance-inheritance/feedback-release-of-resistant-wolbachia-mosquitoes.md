# Equilibria and feedback release in a model of Mendelian resistance and maternal Wolbachia inheritance

Consider adult mosquito populations $A^\eta_i$, where $\eta \in \{U, W\}$ indicates uninfected or *Wolbachia*-infected and $i \in \{1,2,3\}$ the genotype $(r,r)$, $(r,s)$, $(s,s)$ at an insecticide-resistance locus with resistant allele $r$ and susceptible allele $s$. Resistance is inherited by Mendelian rules, *Wolbachia* is inherited maternally with cytoplasmic incompatibility (crosses of uninfected females with infected males are sterile), births depend on the population level $b$ through per-capita rates $m^\eta_i(b)$, deaths occur at rates $\mu^\eta_i$, and a control $v_A \ge 0$ releases infected adults.

**Theorem.**

1. (Invariance) For every non-negative release signal, positive populations stay positive, monomorphic (one genotype) and homogeneous (one infection status) states stay so if nothing else is introduced, and trajectories are uniformly ultimately bounded when $v_A$ is bounded.
2. (Equilibria) Without releases, apart from extinction there are at most six monomorphic equilibria, among them at most four monomorphic homogeneous ones $A^{\eta*}_j(e^\eta \otimes e_i)$, with $A^{\eta*}_j$ the unique positive solution of $m^\eta_i(b^*(\cdot)) = \mu^\eta_i$. All equilibria are unstable except the two homogeneous resistant monomorphic equilibria $A^{\eta*}_r(e^\eta \otimes e_1)$, $\eta \in \{U, W\}$, which are locally asymptotically stable when they exist.
3. (Feedback release) Let $b^{**}$ be the population level at the infected resistant homozygote equilibrium. If $\mu^U_1 + m^W_2(b^{**}) - \mu^W_2 > 0$ and infected resistant adults are released according to an explicit state feedback with margin $\varepsilon$, then every solution converges to the *Wolbachia*-infected resistant equilibrium $A^{W*}_r(e^W \otimes e_1)$, and the releases stop after a finite time. The analogous statement holds for releases of infected susceptible homozygotes under the corresponding condition.

## Expansion

Without releases the uninfected population becomes asymptotically resistant: the resistant homozygote's share tends to $1$ and the other genotypes vanish; a growth-rate dominance lemma ($\dot y/y - \dot z/z \ge \varepsilon$ implies $z/y \to 0$) converts such rate gaps into extinction of the dominated subpopulation. The feedback releases just enough infected adults to keep the infected per-capita growth rate above the uninfected one by $\varepsilon$, which, combined with cytoplasmic incompatibility, drives the uninfected population out; once infection is established the release term vanishes. The analysis shows how insecticide resistance shapes *Wolbachia*-based replacement strategies against dengue vectors.

## Sources

- Pastor Pérez Estigarribia, Pierre-Alexandre Bliman and Christian Schaerer, *Modelling and control of Mendelian and maternal inheritance for biological control of dengue vectors*, arXiv:2011.07766, Theorems 1, 2 and 3 (Section 2), Theorems 4 and 5 (Section 4), Propositions 6 and 7 and Theorems 8 and 9 (Section 5). <https://doi.org/10.48550/arXiv.2011.07766> Published version: ECC 2021 - European Control Conference, Jun 2021, Rotterdam / Virtual, Netherlands.
