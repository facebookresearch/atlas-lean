# Introgression of a multilocus deleterious block

A recipient species receives, each generation, migrants from a donor species fixed for a chromosomal block carrying $L$ equally spaced loci, each with an allele that is deleterious in the recipient, acting multiplicatively. Introgressed material is assumed rare (matings between carriers and multiple crossovers within the block are neglected), and selection, recombination and migration are weak: $sL, cL, m \ll 1$. Let $P(y, t)$ be the frequency of introgressed fragments carrying $y$ consecutive deleterious alleles, $1 \le y \le L$.

**Autosomal block.** With sex-averaged parameters $s_A = (s_F + s_M)/2$ (heterozygous effect per allele), $c_A = (c_F + c_M)/2$ (recombination between adjacent loci) and $m_A = (m_F + m_M)/2$ (migration),

$$\frac{\partial P_A(y, t)}{\partial t} = -\bigl[s_A y + c_A (y - 1)\bigr] P_A(y) + 2 c_A \sum_{y' = y+1}^{L} P_A(y') + m_A \delta_{y, L}. \tag{1}$$

The terms are loss by selection and by recombination splitting the fragment, creation by splitting of longer fragments (each longer fragment yields a fragment of length $y$ in two ways), and influx of whole blocks.

**X-linked block.** For an X (or Z) block not recombining in the heterogametic sex, with $P_X(y) = (P_F(y) + P_M(y))/3$ and $P_F(y) = 2P_X(y)$, $P_M(y) = P_X(y)$ at leading order, $P_X$ satisfies (1) with

$$s_X = \frac{2 s_F + s_M}{3}, \qquad c_X = \frac{2 c_F}{3}, \qquad m_X = \frac{2 m_F + m_M}{3}.$$

Females weigh twice because an X-linked block spends twice as long in females (heterozygous) as in males (hemizygous).

**Equilibrium.** At equilibrium, writing $s, c, m$ for either set of parameters and $\theta = s/c$ for the coupling between loci,

$$P(L) = \frac{m}{sL + c(L - 1)} = \frac{m}{s}\cdot\frac{\theta}{\theta L + L - 1}, \qquad \bigl[s y + c(y-1)\bigr] P(y) = 2c\sum_{y' > y} P(y') \quad (y < L).$$

The block-length distribution therefore depends on the parameters only through $m/s$ and $\theta$. With identical architectures and no sex bias ($s_F = s_M$, $c_F = c_M$), $\theta_X = \tfrac32\theta_A$: deleterious alleles on the X are more tightly coupled and introgress less. For large $L$, the mean deleterious-allele frequency $\bar p = \sum_y y P(y)/L$ behaves like $\frac{m}{S}L^{1 - 2\theta}$ for $\theta \ll 1$, $\frac{m}{2S}(\gamma + \ln 4L)$ for $\theta = 1$, and $\frac{m}{S}(1 + \frac1\theta)$ for $\theta \gg 1$, where $S = sL$ and $\gamma$ is Euler's constant.

## Expansion

The equilibrium is obtained by setting the right side of (1) to zero, starting from $y = L$, where only loss and influx act, and solving downward. The reduction of the X-linked recursion to (1) uses that, under rare introgression, a female carrier passes the block to half her offspring of each sex, while a male carrier passes it only to daughters; at stationarity this gives $P_F = 2P_M$, and averaging the male and female equations with weights $2/3$ and $1/3$ yields the effective parameters.

## Sources

- C. Fraïsse and H. Sachdeva, *The rates of introgression and barriers to genetic exchange between hybridizing species: sex chromosomes vs autosomes*, Genetics 217 (2021), iyaa025, <https://doi.org/10.1093/genetics/iyaa025>, PMCID PMC8045713 (Model and methods; equations (1)–(4); Table 2).
