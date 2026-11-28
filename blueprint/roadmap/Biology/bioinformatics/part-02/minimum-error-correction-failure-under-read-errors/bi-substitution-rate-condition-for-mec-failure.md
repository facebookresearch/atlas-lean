# Bi-substitution rate condition for MEC failure

**Fragment matrix.** Consider a diploid with $l$ heterozygous bi-allelic SNP sites and $N$ aligned reads, each covering at least two sites. The fragment matrix $R \in \{-1, 0, 1\}^{N \times l}$ has $R_{ik} = 1$ (reference allele), $-1$ (alternative allele) or $0$ (site $k$ not covered by read $i$). With $\Omega$ the set of observed entries and $M \in \{\pm 1\}^{N\times l}$ the error-free completed matrix (row $i$ equals $s_ih$, where $h = h_{ex} \in \{\pm 1\}^l$ is the true haplotype vector and $s_i \in \{\pm 1\}$ records the haplotype copy read $i$ comes from),

$$R = P_\Omega(M) + E, \qquad [P_\Omega(M)]_{ij} = \begin{cases} M_{ij}, & (i,j) \in \Omega,\\ 0, & \text{otherwise,}\end{cases}$$

where each nonzero entry of $E$ is $\pm 2$ and flips one observed allele. Such an allele swap is a **bi-substitution**; substitutions to a base that is neither allele are discarded during construction. Let $c(k) = |\{i : (i,k) \in \Omega\}|$ be the coverage of site $k$ and $E(k)$ the number of nonzero entries in column $k$ of $E$; the ratio $E(k)/c(k)$ is the **bi-substitution rate** of site $k$.

**MEC.** For a candidate $h_c \in \{\pm 1\}^l$,

$$\mathrm{MEC}(R, h_c) = \sum_{i=1}^{N} \min\{D(r_i, h_c),\ D(r_i, -h_c)\}, \qquad D(a,b) = \sum_{k=1}^{l} \mathbf{1}[a_k \ne 0,\ b_k \ne 0,\ a_k \ne b_k],$$

where $r_i$ is the $i$-th row of $R$. Minimizing MEC is NP-hard (it can be cast as a max-cut problem).

**Theorem 1 (failure condition).** Suppose every read is at least as close to its true copy as to the opposite one, $D(r_i, s_ih_{ex}) \le D(r_i, -s_ih_{ex})$ for all $i$. If some site $k$ has bi-substitution rate $E(k)/c(k) > 1/2$, then there is $h_d \ne h_{ex}$ with

$$\mathrm{MEC}(R, h_d) < \mathrm{MEC}(R, h_{ex}).$$

A witness is $h_{ex}$ with the sign of entry $k$ inverted.

**Theorem 2 (probability of avoiding the failure condition).** Suppose bi-substitution errors occur independently at each observed entry with probability $p_e$, so $E(j) \sim \mathrm{Binomial}(c(j), p_e)$ independently across sites. Then the probability that no site has bi-substitution rate above $1/2$ is

$$P\{\text{c-MEC}\} = \prod_{j=1}^{l} \ \sum_{n=0}^{\lfloor c(j)/2 \rfloor} \binom{c(j)}{n} p_e^{\,n} (1-p_e)^{c(j)-n}.$$

## Expansion

Theorem 1: by the closeness hypothesis, assigning each read to the haplotype copy $s_ih_{ex}$ it came from attains the minimum, so $\mathrm{MEC}(R,h_{ex}) = \sum_i D(r_i, s_ih_{ex})$. Inverting entry $k$ of the candidate changes, for each of the $c(k)$ reads covering site $k$, the mismatch count at $k$ by $\pm 1$: the $E(k)$ erroneous entries become matches and the $c(k)-E(k)$ correct entries become mismatches. Keeping the orientations $s_i$ gives $\mathrm{MEC}(R,h_d) \le \sum_i D(r_i, s_ih_d) = \mathrm{MEC}(R,h_{ex}) + c(k) - 2E(k)$, which is smaller when $E(k) > c(k)/2$. The source states Theorem 1 without the closeness hypothesis, and it is needed: with $l=2$, $h_{ex}=(1,1)$ and a single read $r=(-1,-1)$ from copy $h_{ex}$ with both entries flipped, $E(1)/c(1)=1$ but $\mathrm{MEC}(R,h_{ex}) = \min\{2,0\} = 0$, so no candidate does better. Theorem 2 multiplies, over independent sites, the binomial probability that site $j$ has at most $\lfloor c(j)/2 \rfloor$ errors.

Because the product runs over all $l$ sites, $P\{\text{c-MEC}\}$ decays geometrically with haplotype length at fixed coverage, and low-coverage sites dominate the failure probability. Plugging in typical error profiles, high-accuracy short reads keep $P\{\text{c-MEC}\}$ near $1$ already at moderate coverage, whereas error-prone long reads need substantially higher coverage; simulations with a max-cut based MEC assembler show switch error decreasing with coverage accordingly.

## Sources

- S. Majidian, M. H. Kahaei, D. de Ridder, "Minimum error correction-based haplotype assembly: Considerations for long read data", PLOS ONE 15 (2020) e0234470, Equations (1)–(9), Theorems 1 and 2, <https://doi.org/10.1371/journal.pone.0234470>, PMCID PMC7292361.
