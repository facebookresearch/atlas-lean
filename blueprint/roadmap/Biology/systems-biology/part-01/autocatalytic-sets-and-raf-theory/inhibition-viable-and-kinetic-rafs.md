# Inhibition-viable and kinetic RAFs: random catalysis bounds and NP-completeness

**Setting.** Let $\mathcal Q = (X, \mathcal R, C, F)$ be a catalytic reaction system with RAFs and closed RAFs as usual.

- An **inhibition assignment** is $I \subseteq X \times \mathcal R$. A subset $\mathcal R'$ is an **$I$-viable RAF** if it is a closed RAF and no reaction of $\mathcal R'$ is inhibited by a molecule of $\mathrm{cl}_{\mathcal R'}(F)$.
- A **kinetic CRS** adds fixed reaction rates $v(r) > 0$ and a diffusion rate $\delta \ge 0$. For $\mathcal R' \subseteq \mathcal R$ let $S_{\mathcal R'}$ be the stoichiometric matrix with rows indexed by the non-food molecules of $\mathrm{supp}(\mathcal R')$ and columns by $\mathcal R'$ (net production of molecule $i$ by reaction $j$), and $v_{\mathcal R'}$ the rate vector. $\mathcal R'$ is a **kinetic RAF** (kRAF) if it is a closed RAF and

    $$S_{\mathcal R'}\, v_{\mathcal R'} \ \ge\ \delta\, \mathbf 1 \quad \text{(componentwise)},$$

    i.e. every non-food molecule of the set is produced at least as fast as it is lost to consumption and diffusion. In particular $S_{\mathcal R'} v_{\mathcal R'} \ge 0$ is necessary.

**Theorem (complexity).**
(a) Deciding whether a CRS with an inhibition assignment has an $I$-viable RAF is NP-complete (the closedness requirement does not change this, since the standard reduction builds closed RAFs).
(b) Deciding whether a kinetic CRS with $\delta = 0$ contains a kRAF is NP-complete (reduction from 3-SAT). Checking whether a *given* RAF is a kRAF takes polynomial time.

**Lemma (random catalysis and inhibition).** Suppose the events "$x$ catalyses $r$" and "$x$ inhibits $r$" are independent over all pairs $(x, r)$, the expected number $c(r)$ of catalysts of $r$ satisfies $c_l \le c(r) \le c_u$, and the expected number of inhibitors of any reaction is at most $\varepsilon$. Let $q_r$ be the probability that $r$ has no catalyst in $X$ or at least one inhibitor in $X$. Then

$$1 - c_u \ \le\ q_r \ \le\ e^{-c_l} + \varepsilon .$$

Under a species stratification of the molecule set and comparable catalysis rates across reactions (expected catalyst numbers within a constant factor $K$), these bounds show that the probability of an RAF is governed by how the average number of reactions catalysed per molecule type compares with the ratio of forward reactions to molecule types: it is small when that ratio-scaled catalysis level $\lambda$ is small and tends to one exponentially fast in $\lambda$ when it is large. For polymer models this ratio grows linearly with maximal polymer length, so the required catalysis rate grows only linearly; this holds for partitioned (for example peptide–RNA) systems as well, and small inhibition rates do not destroy the high-probability regime.

## Expansion

For the lemma, with $p_{x,r}$ and $i_{x,r}$ the catalysis and inhibition probabilities, $1 - q_r = \big(1 - \prod_x (1 - p_{x,r})\big)\prod_x(1 - i_{x,r})$. The first factor is at most $\sum_x p_{x,r} = c(r) \le c_u$, giving the lower bound. For the upper bound, $q_r \le \prod_x(1 - p_{x,r}) + \big(1 - \prod_x(1 - i_{x,r})\big) \le e^{-c(r)} + \sum_x i_{x,r}$. The lower bound controls the probability that a bounded number $\tau$ of primary reactions (those with only food reactants) are all uncatalysed, which upper-bounds the probability of an RAF; the upper bound, combined with geometric growth of the strata and at least linearly many reactions producing each molecule, bounds the probability that some molecule is unproducible, which lower-bounds the probability of an RAF. Since RAFs are found in polynomial time, a practical route to kRAFs is to enumerate RAFs first and test the rate inequality for each.

## Depends on

- [Closed RAFs and the closure of an RAF](closed-raf-sets-and-the-closure-of-an-raf.md)

## Sources

- J. I. Smith, M. Steel, W. Hordijk, "Autocatalytic sets in a partitioned biochemical network", Journal of Systems Chemistry 5 (2014), 2, "The probability of RAFs in general catalytic reaction systems" (conditions (C1)–(C2), species stratification, Theorem 1), "Inhibition" (conditions (C1)–(C3), Theorem 2), "Kinetic RAF framework" (Eq. (2), Theorem 3) and Appendix (Lemma 2, proofs of Theorems 1–3), <https://doi.org/10.1186/1759-2208-5-2> (PMC4034171).
