# Closed RAFs and the closure of an RAF

**Chemical reaction systems.** A catalytic reaction system (CRS) is $\mathcal Q = (X, \mathcal R, C, F)$: a finite set $X$ of molecule types, a food set $F \subseteq X$, a finite set $\mathcal R$ of reactions (pairs of multisets of reactants and products), and a catalysis assignment $C \subseteq X \times \mathcal R$, where $(x, r) \in C$ means that $x$ catalyses $r$. Write $\rho(r)$ and $\pi(r)$ for the sets of reactants and products, and for $\mathcal R' \subseteq \mathcal R$ let $\mathrm{supp}(\mathcal R') = \bigcup_{r \in \mathcal R'} (\rho(r) \cup \pi(r))$. The **closure** $\mathrm{cl}_{\mathcal R'}(F)$ is the smallest $W \subseteq X$ with $F \subseteq W$ and $\pi(r) \subseteq W$ whenever $r \in \mathcal R'$ and $\rho(r) \subseteq W$ (everything buildable from food by reactions of $\mathcal R'$, ignoring catalysis).

**RAF.** RAF sets, their union property and the maxRAF are as in [RAF sets and the maxRAF algorithm](raf-sets-and-the-maxraf-algorithm.md).

**Closed RAF.** An RAF $\mathcal R'$ is **closed** if every $r \in \mathcal R$ with $\rho(r) \subseteq \mathrm{cl}_{\mathcal R'}(F)$ and some catalyst $x \in \mathrm{cl}_{\mathcal R'}(F)$, $(x, r) \in C$, already belongs to $\mathcal R'$ ("every reaction that can occur does occur"). The **closure** $\overline{\mathcal R'}$ of an RAF is obtained by $K_0 = \mathcal R'$, $K_{i+1} = K_i \cup L_i$, where $L_i$ is the set of reactions whose reactants and some catalyst lie in $\mathrm{cl}_{K_i}(F)$, stopping at the first $i$ with $K_{i+1} = K_i$; it is the smallest closed RAF containing $\mathcal R'$, and $\mathcal R'$ is closed iff $\overline{\mathcal R'} = \mathcal R'$. The union of two closed RAFs is an RAF but need not be closed.

**Lemma (a closed RAF is determined by its molecules).** If $\mathcal R'$ is a closed RAF and $W = F \cup \mathrm{supp}(\mathcal R')$, then

$$\mathcal R' = \{ r \in \mathcal R : \rho(r) \subseteq W \text{ and } \exists x \in W,\ (x, r) \in C \}.$$

**Corollary.** For any RAF $\mathcal R'$, its closure $\overline{\mathcal R'}$ can be reconstructed from the set $\mathrm{supp}(\mathcal R')$ and the CRS alone.

## Depends on

- [RAF sets and the maxRAF algorithm](raf-sets-and-the-maxraf-algorithm.md)

## Expansion

For an RAF one has $\mathrm{cl}_{\mathcal R'}(F) = F \cup \mathrm{supp}(\mathcal R')$: every reactant is food-generated and then every product is produced. So conditions 1–2 say exactly that each $r \in \mathcal R'$ has reactants and a catalyst in $W$, giving the inclusion $\subseteq$ in the lemma; closedness gives $\supseteq$. Without closedness the right-hand side is the first closure step $K_1$, and iterating gives the corollary. Closedness matters once inhibition or kinetics are added: if a reaction outside the set could proceed from available reactants and catalysts, its products would be present and could inhibit or deplete the set, so viability notions are stated for closed RAFs.

## Sources

- J. I. Smith, M. Steel, W. Hordijk, "Autocatalytic sets in a partitioned biochemical network", Journal of Systems Chemistry 5 (2014), 2, "Definitions" and "Extensions: closure, inhibition and reaction rates" ("Closed RAFs", Lemma 1, Corollary 1), <https://doi.org/10.1186/1759-2208-5-2> (PMC4034171).
- W. Hordijk, M. Steel, "Detecting autocatalytic, self-sustaining sets in chemical reaction systems", Journal of Theoretical Biology 227 (2004), 451–461, <https://doi.org/10.1016/j.jtbi.2003.11.020>.
